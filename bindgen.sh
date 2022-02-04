#!/bin/env bash

bindgen ffi.h \
  --raw-line "#![allow(nonstandard_style)]" \
  --raw-line "#![allow(deref_nullptr)]" \
  --blocklist-item=Tcl_FreeProc \
  --raw-line "type Tcl_FreeProc = *const ::std::os::raw::c_void;" \
  -o src/ffi.rs -- -DUSE_TCL_STUBS=1