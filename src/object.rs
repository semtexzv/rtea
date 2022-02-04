use std::convert::TryFrom;
use std::ffi::c_void;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use crate::{ffi, Interpreter};
use crate::ffi::{Tcl_IncrRefCount, Tcl_Obj, Tcl_RegisterObjType};

/// A wrapper for [Tcl objects](https://www.tcl.tk/man/tcl/TclLib/Object.html).
///
/// WIP
#[repr(transparent)]
pub struct Object<T> {
    pub(crate) ffi: *mut ffi::Tcl_Obj,
    _p: PhantomData<T>,
}

impl<T: 'static> Object<T> {
    pub fn new(interp: &Interpreter, v: T) -> Self {
        let v = Box::new(v);
        let obj = unsafe { ffi::Tcl_NewObj() };

        unsafe {
            // Sanity check
            assert_eq!((*obj).refCount, 0);
            unsafe { Tcl_IncrRefCount(obj) };

            (*obj).internalRep.ptrAndLongRep.ptr = Box::into_raw(v) as *mut c_void;
            (*obj).internalRep.ptrAndLongRep.value = std::intrinsics::type_id::<T>();
        }
        Self {
            ffi: obj,
            _p: PhantomData,
        }
    }
}

impl<T: 'static> TryFrom<*mut ffi::Tcl_Obj> for Object<T> {
    type Error = ();

    fn try_from(value: *mut Tcl_Obj) -> Result<Self, Self::Error> {
        if value == std::ptr::null_mut() {
            return Err(());
        }
        unsafe {
            if std::intrinsics::type_id::<T>() != (*value).internalRep.ptrAndLongRep.value {
                return Err(());
            }
            ffi::Tcl_IncrRefCount(value);
        }

        Ok(Self {
            ffi: value,
            _p: PhantomData,
        })
    }
}

impl<T: 'static> Deref for Object<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            ((*self.ffi).internalRep.ptrAndLongRep.ptr as *const c_void as *const T)
                .as_ref()
                .expect("Object was unexpectedly null")
        }
    }
}

impl<T: 'static> DerefMut for Object<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            ((*self.ffi).internalRep.ptrAndLongRep.ptr as *mut c_void as *mut T)
                .as_mut()
                .expect("Object was unexpectedly null")
        }
    }
}

impl<T> Drop for Object<T> {
    fn drop(&mut self) {
        unsafe {
            // Sanity check
            assert!((*self.ffi).refCount > 0);

            ffi::Tcl_DecrRefCount(self.ffi);
            if (*self.ffi).refCount == 0 {
                std::mem::drop(Box::from_raw((*self.ffi).internalRep.ptrAndLongRep.ptr));
            }
        }
    }
}

impl<T> Object<T> {}

/// A wrapper for [Tcl object types](https://www.tcl.tk/man/tcl/TclLib/ObjectType.html).
///
/// WIP
#[repr(transparent)]
#[derive(Debug)]
pub struct ObjType {
    pub(crate) ffi: ffi::Tcl_ObjType,
}
