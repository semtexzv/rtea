use std::convert::TryFrom;
use std::ffi::c_void;
use std::ffi::CStr;
use std::ffi::CString;
use std::mem::transmute;
use std::os::raw::c_char;

use crate::Object;
use crate::ffi;
use crate::ffi::{ClientData, Tcl_AttemptAlloc, Tcl_CmdDeleteProc, Tcl_CmdProc, Tcl_DeleteCommand, Tcl_GetString, Tcl_GetStringFromObj, Tcl_InitStubs, Tcl_Interp, Tcl_SetResult};

/// A wrapper around a [Tcl](https://www.tcl.tk) interpreter object.
///
/// This is a wrapper around the Tcl interpreter object that leverages the
/// Stubs interface.  It makes assumptions about the interface (such as
/// stability of function pointers) that are made by the underlying stubs
/// implementation.  However, as a deliberate nod to the importance of the
/// borrow checker and other rust conventions, it obtains the stubs table on
/// each `command` rather than caching the version passed during the call to
/// an initialization routine.  While this sacrifices runtime performance
/// (extra indirection), it fits more with Rust paradigms and should reduce
/// the risk of trying to use the API without an associated interpeter.
#[repr(C)]
pub struct Interpreter {
    ffi: ffi::Tcl_Interp,
}


type CmdProc = fn(interp: &Interpreter, args: Vec<&str>) -> Result<TclStatus, String>;

const TCL_STUB_MAGIC: u32 = 0xFCA3BACF; // Tcl 8.x extension

/// A wrapper for Tcl return status codes.
///
/// This is a simple wrapper around the expected return codes for Tcl
/// commands.  `Ok` and `Error` are the most common ones, but the others have
/// specific meanings under certain conditions (e.g., binding handlers in
/// Tk).  See the appropriate documentation for specific behavior.
#[repr(C)]
#[derive(Debug, PartialEq)]
pub enum TclStatus {
    Ok = 0,
    Error = 1,
    Return = 2,
    Break = 3,
    Continue = 4,
}

impl From<i32> for TclStatus {
    fn from(v: i32) -> Self {
        assert!(v >= 0 && v <= 4);
        unsafe { std::mem::transmute(v) }
    }
}

impl Into<i32> for TclStatus {
    fn into(self) -> i32 {
        unsafe { std::mem::transmute(self) }
    }
}

/// A wrapper for values passed to Tcl's [unload](https://www.tcl.tk/man/tcl/TclCmd/unload.html) function.
#[repr(isize)]
pub enum TclUnloadFlag {
    /// Inidicates the interpreter is exiting but that the module's code is
    /// not being unmapped.
    DetachFromInterpreter = 1 << 0,
    /// Inidicates the last interpreter is detaching and the module is about
    /// to be unmapped from the process.
    DetachFromProcesss = 1 << 1,
}

const _TCL_STATIC: *const c_void = 0 as *const c_void;
const _TCL_VOLATILE: *const c_void = 1 as *const c_void;
const TCL_DYNAMIC: *const c_void = 3 as *const c_void;

#[repr(transparent)]
struct Stubs {
    ffi: ffi::TclStubs,
}

/// Error codes for unwrapping a Tcl interpreter.
///
/// These exist primarily for debugging and advanced use-cases.  Unless you
/// are calling [from_raw](Interpreter::from_raw), you should not need to worry about these.
#[derive(Debug)]
pub enum Error {
    NullInterpreter,
    NullStubs,
    InvalidStubs,
    TclError(String),
}

impl<'a> Interpreter {
    /// Converts a raw pointer to a Tcl interpreter into a Rust reference.
    ///
    /// Most users should not need to use this function because a reference is
    /// already passed to the appropriate functions.  This is public because
    /// of how the [module_init](rtea_proc::module_init) macro works.
    pub fn from_raw(interpreter: *const ffi::Tcl_Interp) -> Result<&'a Interpreter, Error> {
        if let Some(interpreter) = unsafe { (interpreter as *const Interpreter).as_ref() } {
            Ok(interpreter)
        } else {
            Err(Error::NullInterpreter)
        }
    }

    pub(crate) fn as_ffi(&self) -> *mut ffi::Tcl_Interp {
        (&self.ffi) as *const _ as *mut _
    }

    /// Informs the Tcl interpreter that the given package and version is available.
    pub fn provide_package(&self, name: &str, version: &str) -> Result<TclStatus, String> {
        let name =
            CString::new(name).map_err(|_| "unexpected Nul in package version".to_string())?;
        let version =
            CString::new(version).map_err(|_| "unexpected Nul in package version".to_string())?;
        Ok(TclStatus::Ok)
    }

    /// Registers the command given by `proc` as `name`.
    pub fn create_command<F>(&self, name: &str, proc: F) -> Result<TclStatus, String>
        where F: FnMut(&Interpreter, Vec<&str>) -> Result<TclStatus, String>
    {
        let name = CString::new(name).map_err(|_| "unexpected Nul in command name".to_string())?;
        let proc = Box::new(proc);

        // type TclCmdProc = extern "C" fn(
        //     data: *const c_void,
        //     interp: *const Interpreter,
        //     argc: usize,
        //     argv: *const *const i8,
        // ) -> TclStatus;
        unsafe extern "C" fn wrapper_proc<F>(
            data: *mut c_void,
            i: *mut Tcl_Interp,
            argc: i32,
            argv: *mut *const i8,
        ) -> i32
            where F: FnMut(&Interpreter, Vec<&str>) -> Result<TclStatus, String>
        {
            let interp = Interpreter::from_raw(i).expect("Tcl passed bad interpreter");
            let raw_args = unsafe { std::slice::from_raw_parts(argv, argc as _) };
            let mut args = Vec::with_capacity(raw_args.len());
            for arg in raw_args {
                args.push(
                    unsafe { std::ffi::CStr::from_ptr(*arg) }
                        .to_str()
                        .expect("invalid args from Tcl"),
                );
            }
            let mut f = Box::from_raw(data as *mut F);
            let callback = f(interp, args);

            let res = callback.unwrap_or_else(|s| {
                interp.set_result(&s);
                TclStatus::Error
            }).into();
            // Forget the function again
            let _ = Box::into_raw(f);
            res
        }

        unsafe {
            ffi::Tcl_CreateCommand(
                self.as_ffi(),
                name.as_ptr(),
                Some(wrapper_proc::<F>),
                Box::into_raw(proc) as ClientData,
                None,
            )
        };
        Ok(TclStatus::Ok)
    }
    /// Attaches the `StatefulCommand` to a Tcl interpreter.
    ///
    /// This exposes the instantiated `StatefulCommand` to the given
    /// interpreter.  This should allow exposing a command to multiple
    /// interpreters (or as aliases in the same interpreter) for advanced
    /// functionality. While the borrow checker should prevent some misuses
    /// (type is passed by ownership), this has not been heavily tested for
    /// every type `T`.
    pub fn attach_stateful_command<F, T>(&self, name: &str, state: T, cmd: F) -> Result<TclStatus, String>
        where F: Fn(&Interpreter, &T, Vec<&str>) -> Result<TclStatus, String>,
              T: 'static
    {
        let state = Box::new((cmd, state));
        let name = CString::new(name).map_err(|_| "unexpected Nul in command name".to_string())?;

        // Simple wrapper of the Rust function and data to work with Tcl's API.
        unsafe extern "C" fn wrapper_proc<F, T>(
            state: ffi::ClientData,
            i: *mut Tcl_Interp,
            argc: ::std::os::raw::c_int,
            argv: *mut *const i8,
        ) -> i32
            where F: Fn(&Interpreter, &T, Vec<&str>) -> Result<TclStatus, String>
        {
            let interp = Interpreter::from_raw(i).expect("Tcl passed bad interpreter");
            let raw_args = unsafe { std::slice::from_raw_parts(argv, argc as _) };
            let mut args = Vec::with_capacity(raw_args.len());
            for arg in raw_args {
                args.push(
                    unsafe { std::ffi::CStr::from_ptr(*arg) }
                        .to_str()
                        .expect("invalid args from Tcl"),
                );
            }

            let state = unsafe { (state as *const (F, T)).as_ref() }.expect("data command corrupted!");

            (state.0)(interp, &state.1, args).unwrap_or_else(|s| {
                interp.set_result(&s);
                TclStatus::Error
            }).into()
        }

        // Simple function to restore the `StatefulCommand` to Rust's
        // understanding to allow Rust's RAII code to kick in.
        unsafe extern "C" fn free_state<F, T>(state: *mut c_void) {
            // This relies on Tcl to properly track the command state and
            // invoke this at the appropriate moment.  Retaking ownership
            // of the underlying pointer ensures the destructor gets called
            unsafe { Box::<(F, T)>::from_raw(state as *mut _) };
        }

        let command = unsafe {
            ffi::Tcl_CreateCommand(
                self.as_ffi(),
                name.as_ptr(),
                Some(wrapper_proc::<F, T>),
                Box::<(F, T)>::into_raw(state) as ClientData,
                Some(free_state::<F, T>),
            )
        };

        Ok(TclStatus::Ok)
    }

    /// Delets the given command.
    ///
    /// This function attempts to delete the command `name` in the
    /// interpreter.  If it exists, `true` is returned, otherwise `false` is
    /// returned.  An error is only returned when the given `name` contains
    /// Nul characters and is therefore not a valid Tcl string.
    pub fn delete_command(&self, name: &str) -> Result<bool, String> {
        let name = CString::new(name).map_err(|_| "unexpected Nul in command name".to_string())?;

        let ret = unsafe { ffi::Tcl_DeleteCommand(self.as_ffi(), name.as_ptr()) };

        Ok(ret == 0)
    }

    pub fn get_raw_obj_result(&self) -> *mut ffi::Tcl_Obj {
        unsafe {
            ffi::Tcl_GetObjResult(self.as_ffi())
        }
    }
    /// Get the current result object for the interpreter.
    pub fn get_obj_result<T: 'static>(&self) -> Object<T> {
        unsafe {
            let obj = ffi::Tcl_GetObjResult(self.as_ffi());
            Object::<T>::try_from(obj).unwrap()
        }
    }

    /// Evaluate a Tcl script.
    ///
    /// Evaluates the given string as a Tcl script.  If the script return
    /// `TclStatus::Error`, then the associated error message is passed back
    /// as `Err`.  Otherwise the last commands return value is passed through
    /// as is.
    pub fn eval(&self, script: &str) -> Result<TclStatus, String> {
        if script.len() > 1 << 31 {
            return Err(
                "Tcl versions prior to 9.0 do not support scripts greater than 2 GiB".to_string(),
            );
        }
        let res = unsafe {
            ffi::Tcl_EvalEx(
                self.as_ffi(),
                script.as_ptr() as *const c_char,
                script.len() as _,
                0,
            ).into()
        };
        if res == TclStatus::Error {
            Err(self.get_raw_string(self.get_raw_obj_result()).to_string())
        } else {
            Ok(res)
        }
    }

    /// Set the interpreter's current result value.
    ///
    /// When inside command logic, this can be used to set the return value
    /// visible to the invoking Tcl script.
    pub fn set_result(&self, text: &str) {
        let tcl_str = self
            .alloc(text.len() + 1)
            .expect("propagating memory failure in Tcl");

        tcl_str[..text.len()].copy_from_slice(text.as_bytes());

        if let Some(terminator) = tcl_str.last_mut() {
            *terminator = 0;
        }

        unsafe {
            Tcl_SetResult(self.as_ffi(), tcl_str.as_mut_ptr() as *mut c_char, TCL_DYNAMIC)
        }
    }

    pub fn set_obj_result<T>(&self, obj: Object<T>) {
        unsafe {
            ffi::Tcl_SetObjResult(self.as_ffi(), obj.ffi);
        }
    }

    pub fn get_raw_string(&self, obj: *mut ffi::Tcl_Obj) -> &str {
        let mut len: i32 = 0;
        let raw = unsafe {
            let ptr = Tcl_GetStringFromObj(obj, &mut len as *mut _) as *mut u8;
            let data = std::slice::from_raw_parts(ptr, len as usize);
            std::str::from_utf8(data)
        };
        raw.expect("Invalid UTF-8 from Tcl")
    }

    /// Gets the string associated with the Tcl object.
    pub fn get_string<T: 'static>(&self, obj: &Object<T>) -> &str {
        self.get_raw_string(obj.ffi)
    }

    /// Allocates Tcl-managed memory.
    ///
    /// Allocates memory that is directly managed by Tcl.  This is required
    /// for certain interfaces (e.g., bytes representation of Tcl objects)
    /// and convenient for others (e.g., creating a Nul terminated string
    /// from a Rust `String`).
    pub fn alloc(&self, size: usize) -> Option<&mut [u8]> {
        if size >= 1 << 32 {
            return None;
        }
        let ptr = unsafe {
            Tcl_AttemptAlloc(size as std::os::raw::c_uint)
        };

        if ptr.is_null() {
            None
        } else {
            unsafe {
                // We've checked that it is not null and therefore trust Tcl
                Some(std::slice::from_raw_parts_mut(ptr as *mut u8, size))
            }
        }
    }
}
