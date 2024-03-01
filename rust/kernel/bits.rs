// SPDX-License-Identifier: GPL-2.0

//! Bit manipulation helpers
//!
//! C header: [`include/linux/bits.h`](srctree/include/linux/bits.h)

//use crate::static_assert;

/// Generate a mask where all bits >= `h` and <= `l` are set
///
/// This is a re-implementation in rust of `GENMASK`
pub const fn genmask(h: u32, l: u32) -> u32 {
    //static_assert!(h >= l);
    //static_assert!(h < 32);
    ((!0u32) - (1 << l) + 1) & ((!0u32) >> (32 - 1 - h))
}
