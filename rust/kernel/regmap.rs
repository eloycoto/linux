// SPDX-License-Identifier: GPL-2.0

//! Register map access API.
//!
//! C header: [`include/linux/regmap.h`](srctree/include/linux/regmap.h)

#[cfg(CONFIG_REGMAP_I2C)]
use crate::i2c;
use crate::{
    bindings,
    error::{code::*, to_result, Error, Result},
    macros::paste,
    sync::Arc,
};
use core::{marker::PhantomData, mem::MaybeUninit};

/// Type of caching
#[repr(u32)]
pub enum CacheType {
    /// Don't cache anything
    None = bindings::regcache_type_REGCACHE_NONE,
    /// Use RbTree caching
    RbTree = bindings::regcache_type_REGCACHE_RBTREE,
    /// Use Flat caching
    Flat = bindings::regcache_type_REGCACHE_FLAT,
    /// Use Maple caching
    Maple = bindings::regcache_type_REGCACHE_MAPLE,
}

/// Register map
///
/// # Examples
///
/// ```
/// let regmap = Regmap::init_i2c(i2c, &config);
/// ```
pub struct Regmap {
    ptr: *mut bindings::regmap,
}
impl Regmap {
    #[cfg(CONFIG_REGMAP_I2C)]
    /// Initialize a [`Regmap`] instance for an `i2c` device.
    pub fn init_i2c<T: ConfigOps>(i2c: &i2c::Client, config: &Config<T>) -> Self {
        let regmap = unsafe { bindings::regmap_init_i2c(i2c.raw_client(), &config.raw) };

        Self { ptr: regmap }
    }

    /// Allocate regmap [`Fields`]
    ///
    /// This function allocate regmap fields from the `reg_fields` descriptors
    pub fn alloc_fields<const N: usize>(
        self: &Arc<Regmap>,
        descs: &'static FieldDescs<N>,
    ) -> Result<Fields<N>> {
        let mut rm_fields = [core::ptr::null_mut(); N];
        to_result(unsafe {
            bindings::regmap_field_bulk_alloc(
                self.ptr,
                &mut rm_fields[0],
                descs.0.as_ptr(),
                descs.0.len() as i32,
            )
        })?;

        Ok(Fields {
            rm_fields,
            _regmap: self.clone(),
        })
    }

    /// Return the raw pointer of this regmap
    pub fn as_ptr(&self) -> *mut bindings::regmap {
        self.ptr
    }
}

impl Drop for Regmap {
    fn drop(&mut self) {
        unsafe { bindings::regmap_exit(self.ptr) }
    }
}

/// Field Descriptors
///
/// FieldDescriptors can be created by calling the [`define_regmap_field_descs`] macro.
pub struct FieldDescs<const N: usize>([bindings::reg_field; N]);

impl<const N: usize> FieldDescs<N> {
    // macro use only
    #[doc(hidden)]
    pub const fn new(fields: [bindings::reg_field; N]) -> Self {
        Self(fields)
    }

    /// Number of fields being held by `FieldDescs<N>`
    ///
    /// This function should be used to retrieve the number of fields that were
    /// created when calling [`define_regmap_field_descs`].
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::regmap::{define_regmap_field_descs, Fields};
    ///
    /// define_regmap_field_descs!(DESCS, {
    ///     {pid, 0x3, kernel::regmap::access::READ, { value => raw([7:0], ro) }},
    /// });
    ///
    /// struct Registrations {
    ///    fields: Fields<{ DESCS.count() }>,
    /// }
    /// ```
    pub const fn count(&self) -> usize {
        N
    }
}

/// Regmap fields
///
/// # Invariants
///
/// `rm_fields` is garanteed to contains valid and initialized `regmap_field`s.
///
pub struct Fields<const N: usize> {
    rm_fields: [*mut bindings::regmap_field; N],

    // Each regmap_field hold a pointer to the `struct regmap` instance, so we need to keep a copy
    // of the wrapper around.
    _regmap: Arc<Regmap>,
}
impl<const N: usize> Fields<N> {
    /// Get field `index`
    pub fn index(&mut self, index: usize) -> *mut bindings::regmap_field {
        self.rm_fields[index]
    }

    // macro use only
    #[doc(hidden)]
    pub fn read(&mut self, index: usize) -> Result<core::ffi::c_uint> {
        let mut val = 0;

        // Make sure we don't panic if the index is out of bound.
        if index >= N {
            return Err(EINVAL);
        }

        // SAFETY: By the type invariants, we are garanteed that all rm_fields entries point
        // to valid and initialized values, hence it is safe to make this FFI call.
        let ret = unsafe { bindings::regmap_field_read(self.rm_fields[index], &mut val) };
        if ret < 0 {
            return Err(Error::from_errno(ret));
        }

        Ok(val)
    }
}

unsafe impl<const N: usize> Send for Fields<N> {}

/// Helper macro for [`Config`] to create methods to set a fields from [`regmap_config`]
///
/// The following code will create a method named `with_max_register`:
/// ```
/// config_with!(max_register: u32);
/// ```
macro_rules! config_with {
    ($(#[$meta:meta])* $name:ident: $type:ty) => {
        config_with!($(#[$meta])* $name: $type, $name);
    };

    ($(#[$meta:meta])* $name:ident: $type:ty, $e:expr) => {
        paste! {
            $(#[$meta])*
            pub const fn [<with_$name>](mut self, $name: $type) -> Self {
                self.raw.$name = $e;
                self
            }
        }
    };
}

// macro use only
#[doc(hidden)]
pub trait ConfigOps {
    fn is_readable_reg(reg: u32) -> bool;
    fn is_writeable_reg(reg: u32) -> bool;
    fn is_volatile_reg(reg: u32) -> bool;
    fn is_precious_reg(reg: u32) -> bool;
    fn is_readable_noinc_reg(reg: u32) -> bool;
    fn is_writeable_noinc_reg(reg: u32) -> bool;
}

/// Regmap Configuration
pub struct Config<T: ConfigOps> {
    raw: bindings::regmap_config,
    _phantom: PhantomData<T>,
}
impl<T: ConfigOps> Config<T> {
    /// Create a new regmap Config
    pub const fn new(reg_bits: i32, val_bits: i32) -> Self {
        let cfg = MaybeUninit::<bindings::regmap_config>::zeroed();
        let mut cfg = unsafe { cfg.assume_init() };

        cfg.reg_bits = reg_bits;
        cfg.val_bits = val_bits;
        cfg.writeable_reg = Some(Self::writeable_reg_callback);
        cfg.readable_reg = Some(Self::readable_reg_callback);
        cfg.volatile_reg = Some(Self::volatile_reg_callback);
        cfg.precious_reg = Some(Self::precious_reg_callback);
        cfg.writeable_noinc_reg = Some(Self::writeable_noinc_reg_callback);
        cfg.readable_noinc_reg = Some(Self::readable_noinc_reg_callback);

        Self {
            raw: cfg,
            _phantom: PhantomData,
        }
    }

    config_with!(
        /// Specifies the maximum valid register address.
        max_register: u32
    );

    config_with!(
        /// Type of caching being performed.
        cache_type: CacheType, cache_type as _
    );

    unsafe extern "C" fn writeable_reg_callback(_dev: *mut bindings::device, reg: u32) -> bool {
        T::is_writeable_reg(reg)
    }

    unsafe extern "C" fn readable_reg_callback(_dev: *mut bindings::device, reg: u32) -> bool {
        T::is_readable_reg(reg)
    }

    unsafe extern "C" fn volatile_reg_callback(_dev: *mut bindings::device, reg: u32) -> bool {
        T::is_volatile_reg(reg)
    }

    unsafe extern "C" fn precious_reg_callback(_dev: *mut bindings::device, reg: u32) -> bool {
        T::is_precious_reg(reg)
    }

    unsafe extern "C" fn writeable_noinc_reg_callback(
        _dev: *mut bindings::device,
        reg: u32,
    ) -> bool {
        T::is_writeable_noinc_reg(reg)
    }

    unsafe extern "C" fn readable_noinc_reg_callback(
        _dev: *mut bindings::device,
        reg: u32,
    ) -> bool {
        T::is_readable_noinc_reg(reg)
    }
}

/// Definitions describing how registers can be accessed.
pub mod access {
    /// Register can be read from.
    pub const READ: u32 = 0b000001;
    /// Register can be written to.
    pub const WRITE: u32 = 0b000010;
    /// Register should not be read outside of a call from the driver.
    pub const PRECIOUS: u32 = 0b000100;
    /// Register value can't be cached.
    pub const VOLATILE: u32 = 0b001000;
    /// Register supports multiple write operations without incrementing the register number.
    pub const WRITE_NO_INC: u32 = 0b010000;
    /// Register supports multiple read operations without incrementing the register number.
    pub const READ_NO_INC: u32 = 0b100000;

    /// Register can be read from and written to.
    pub const RW: u32 = READ | WRITE;
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_check_access {
    ($type:ident, $access:expr, $reg:ident, $addr:literal) => {
        if kernel::regmap::access::$type & $access > 0 && $reg == $addr {
            return true;
        }
    };
}
// macro use only
#[doc(hidden)]
pub use regmap_check_access;

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_field_bit {
    ($field_name:ident, $reg:literal, $pos:literal, rw) => {
        $crate::regmap_field_bit!($field_name, $reg, $pos, reserved);
        $crate::regmap_field_bit!($field_name, _ro);
        $crate::regmap_field_bit!($field_name, _wo);
    };

    ($field_name:ident, $reg:literal, $pos:literal, ro) => {
        $crate::regmap_field_bit!($field_name, $reg, $pos, reserved);
        $crate::regmap_field_bit!($field_name, _ro);
    };

    ($field_name:ident, $reg:literal, $pos:literal, wo) => {
        $crate::regmap_field_bit!($field_name, $reg, $pos, reserved);
        $crate::regmap_field_bit!($field_name, _wo);
    };

    ($field_name:ident, $reg:literal, $pos:literal, reserved) => {
        kernel::macros::paste! {
            struct [<_Bit $pos >];
        }

        impl $field_name {
            pub(crate) const fn reg_field() -> bindings::reg_field {
                bindings::reg_field {
                    reg: $reg,
                    lsb: $pos,
                    msb: $pos + 1,
                    id_offset: 0,
                    id_size: 0,
                }
            }

            #[allow(dead_code)]
            pub(crate) const fn mask() -> u32 {
                kernel::bits::genmask($pos, $pos)
            }
        }
    };

    ($field_name:ident, _ro) => {
        impl $field_name {
            #[allow(dead_code)]
            pub(crate) fn is_set<const N: usize>(fields: &mut regmap::Fields<N>) -> Result<bool> {
                let field = unsafe { fields.index(Self::id() as usize) };
                let mut val: core::ffi::c_uint = 0;
                kernel::error::to_result(unsafe { bindings::regmap_field_read(field, &mut val) })?;
                Ok(val == 1)
            }
        }
    };

    ($field_name:ident, _wo) => {
        impl $field_name {
            #[allow(dead_code)]
            pub(crate) fn set<const N: usize>(fields: &mut regmap::Fields<N>) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_write(field, 1) })
            }

            #[allow(dead_code)]
            pub(crate) fn force_set<const N: usize>(fields: &mut regmap::Fields<N>) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_force_write(field, 1) })
            }

            #[allow(dead_code)]
            pub(crate) fn clear<const N: usize>(fields: &mut regmap::Fields<N>) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_write(field, 0) })
            }

            #[allow(dead_code)]
            pub(crate) fn force_clear<const N: usize>(fields: &mut regmap::Fields<N>) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_force_write(field, 0) })
            }
        }
    };
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_field_enum {
    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], ro, {
        $($k:ident = $v:literal,)+ }) => {
        $crate::regmap_field_enum!($field_name, $reg, [$msb:$lsb], reserved, { $($k = $v,)+ });
        $crate::regmap_field_enum!($field_name, _ro);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], rw, {
        $($k:ident = $v:literal,)+ }) => {
        $crate::regmap_field_enum!($field_name, $reg, [$msb:$lsb], reserved, { $($k = $v,)+ });
        $crate::regmap_field_enum!($field_name, _ro);
        $crate::regmap_field_enum!($field_name, _wo);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], wo, {
        $($k:ident = $v:literal,)+ }) => {
        $crate::regmap_field_enum!($field_name, $reg, [$msb:$lsb], reserved, { $($k = $v,)+ });
        $crate::regmap_field_enum!($field_name, _wo);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], reserved, {
        $($k:ident = $v:literal,)+ }) => {
        kernel::macros::seq!(i in $lsb..=$msb {
            kernel::macros::paste! {
                struct [<_Bit $i>];
            }
        });

        kernel::macros::paste! {
            #[repr(u32)]
            #[allow(non_camel_case_types)]
            pub(crate) enum [<$field_name _enum>] {
                $($k = $v,)+
            }

            impl TryFrom<core::ffi::c_uint> for [<$field_name _enum>] {
                type Error = kernel::error::Error;

                fn try_from(raw_value: core::ffi::c_uint) -> Result<Self> {
                    match raw_value {
                        $($v => Ok(Self::$k),)+
                        _ => Err(kernel::error::code::EINVAL),
                    }
                }
            }

            impl $field_name {
                pub(crate) const fn reg_field() -> bindings::reg_field {
                    bindings::reg_field {
                        reg: $reg,
                        lsb: $lsb,
                        msb: $msb,
                        id_offset: 0,
                        id_size: 0,
                    }
                }

                #[allow(dead_code)]
                pub(crate) const fn mask() -> u32 {
                    kernel::bits::genmask($msb, $lsb)
                }
            }
        }
    };

    ($field_name:ident, _ro) => {
        kernel::macros::paste! {
            impl $field_name {
                #[allow(dead_code)]
                pub(crate) fn read<const N: usize>(fields: &mut regmap::Fields<N>) -> Result<[<$field_name _enum>]> {
                    [<$field_name _enum>]::try_from(fields.read(Self::id() as usize)?)
                }
            }
        }
    };

    ($field_name:ident, _wo) => {
        kernel::macros::paste! {
            impl $field_name {
                #[allow(dead_code)]
                pub(crate) fn write<const N: usize>(fields: &mut regmap::Fields<N>, val: [<$field_name _enum>]) -> Result {
                    let field = unsafe { fields.index(Self::id() as usize) };
                    kernel::error::to_result(unsafe { bindings::regmap_field_write(field, val as _) })
                }

                #[allow(dead_code)]
                pub(crate) fn force_write<const N: usize>(fields: &mut regmap::Fields<N>, val: [<$field_name _enum>]) -> Result {
                    let field = unsafe { fields.index(Self::id() as usize) };
                    kernel::error::to_result(unsafe { bindings::regmap_field_force_write(field, val as _) })
                }
            }
        }
    };
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_field_raw {
    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], rw) => {
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], reserved);
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], _ro);
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], _wo);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], ro) => {
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], reserved);
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], _ro);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], wo) => {
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], reserved);
        $crate::regmap_field_raw!($field_name, $reg, [$msb:$lsb], _wo);
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], reserved) => {
        kernel::macros::seq!(i in $lsb..=$msb {
            kernel::macros::paste! {
                struct [<_Bit $i>];
            }
        });

        impl $field_name {
            pub(crate) const fn reg_field() -> bindings::reg_field {
                bindings::reg_field {
                    reg: $reg,
                    lsb: $lsb,
                    msb: $msb,
                    id_offset: 0,
                    id_size: 0,
                }
            }

            #[allow(dead_code)]
            pub(crate) const fn mask() -> u32 {
                kernel::bits::genmask($msb, $lsb)
            }
        }
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], _ro) => {
        impl $field_name {
            #[allow(dead_code)]
            pub(crate) fn read<const N: usize>(
                fields: &mut regmap::Fields<N>,
            ) -> Result<core::ffi::c_uint> {
                fields.read(Self::id() as usize)
            }

            #[allow(dead_code)]
            pub(crate) fn test_bits<const N: usize>(
                fields: &mut regmap::Fields<N>,
                bits: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_test_bits(field, bits) })
            }
        }
    };

    ($field_name:ident, $reg:literal, [$msb:literal:$lsb:literal], _wo) => {
        impl $field_name {
            #[allow(dead_code)]
            pub(crate) fn write<const N: usize>(
                fields: &mut regmap::Fields<N>,
                val: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_write(field, val as _) })
            }

            #[allow(dead_code)]
            pub(crate) fn force_write<const N: usize>(
                fields: &mut regmap::Fields<N>,
                val: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe {
                    bindings::regmap_field_force_write(field, val as _)
                })
            }

            #[allow(dead_code)]
            pub(crate) fn update_bits<const N: usize>(
                fields: &mut regmap::Fields<N>,
                mask: core::ffi::c_uint,
                val: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe {
                    bindings::regmap_field_update_bits(field, mask, val)
                })
            }

            #[allow(dead_code)]
            pub(crate) fn force_update_bits<const N: usize>(
                fields: &mut regmap::Fields<N>,
                mask: core::ffi::c_uint,
                val: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe {
                    bindings::regmap_field_force_update_bits(field, mask, val)
                })
            }

            #[allow(dead_code)]
            pub(crate) fn set_bits<const N: usize>(
                fields: &mut regmap::Fields<N>,
                bits: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_set_bits(field, bits) })
            }

            /// Clear the register bits
            #[allow(dead_code)]
            pub(crate) fn clear_bits<const N: usize>(
                fields: &mut regmap::Fields<N>,
                bits: core::ffi::c_uint,
            ) -> Result {
                let field = unsafe { fields.index(Self::id() as usize) };
                kernel::error::to_result(unsafe { bindings::regmap_field_clear_bits(field, bits) })
            }
        }
    };
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_fields {
    ($type:ident, $reg:ident, $name:ident, $($t:tt)*) => {
        kernel::macros::paste! {
            #[allow(non_camel_case_types)]
            pub(crate) struct $name;

            impl $name {
                #[allow(dead_code)]
                pub(crate) const fn id() -> super::Fields {
                    super::Fields::[<$reg _ $name>]
                }
            }

            $crate::[<regmap_field_ $type>]!($name, $($t)*);
        }
    };
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_reg_field {
    ($reg_name:ident, $field_name:ident) => {
        register::$reg_name::$field_name::reg_field()
    };
}

// macro use only
#[doc(hidden)]
#[macro_export]
macro_rules! regmap_count_fields {
    () => { 0usize };
    ($type:ident $($rhs:ident)*) => { 1 + $crate::regmap_count_fields!($($rhs)*) };
}

/// Define regmap field descriptors
#[macro_export]
macro_rules! define_regmap_field_descs {
    ($name:ident, {
        $( {
            $reg_name:ident, $reg_addr:literal, $access:expr, {
                $($field_name:ident => $type:ident($($x:tt),*)),*,
            }
        }),+
    }) => {
        mod register {
            use kernel::regmap::ConfigOps;

            kernel::macros::paste! {
                $(
                    pub(crate) mod $reg_name {
                        use kernel::{bindings, error::{Result}, regmap};
                        $( $crate::regmap_fields!($type, $reg_name, $field_name, $reg_addr, $($x),*); )*

                        #[allow(dead_code)]
                        pub(crate) const fn addr() -> u32 {
                            $reg_addr
                        }
                    }
                )+

                #[repr(u32)]
                #[allow(non_camel_case_types)]
                pub(crate) enum Fields {
                    $($(
                        [<$reg_name _ $field_name>],
                    )*)+
                }

                pub(crate) struct AccessOps;
                impl ConfigOps for AccessOps {
                    fn is_readable_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(READ, $access, reg, $reg_addr);
                        )+

                        false
                    }

                    fn is_writeable_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(WRITE, $access, reg, $reg_addr);
                        )+

                        false
                    }

                    fn is_volatile_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(VOLATILE, $access, reg, $reg_addr);
                        )+

                        false
                    }

                    fn is_precious_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(PRECIOUS, $access, reg, $reg_addr);
                        )+

                        false
                    }

                    fn is_writeable_noinc_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(WRITE_NO_INC, $access, reg, $reg_addr);
                        )+

                        false
                    }

                    fn is_readable_noinc_reg(reg: u32) -> bool {
                        $(
                            kernel::regmap::regmap_check_access!(READ_NO_INC, $access, reg, $reg_addr);
                        )+

                        false
                    }
                }
            }
        }

        const $name: regmap::FieldDescs<{$crate::regmap_count_fields!($($($type)*)+)}> =
            regmap::FieldDescs::new([
                $(
                    $(
                        $crate::regmap_reg_field!($reg_name, $field_name)
                    ),*
                ),+
            ]);
    };
}
pub use define_regmap_field_descs;
