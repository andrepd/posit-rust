//! Miscellaneous small utilities, lifted from open source. See section for source and license.

//

// Source: https://github.com/Jules-Bertholet/fallthrough/blob/1f08fc38c2aa3b10a66e6ba45d98cdaecd6bc667/src/lib.rs
//
// Copyright (c) 2023 Jules Bertholet
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#[macro_export]
macro_rules! fallthrough {
    ($scrutinee:expr $(,)?) => {
        match $scrutinee {}
    };
    ($scrutinee:expr, $first_pat:pat $(if $first_guard:expr)? => $first_body:expr $(, $label:lifetime $(: $pat:pat $(if $guard:expr)? => $body:expr)?)* $(,)?) => {
        $crate::fallthrough_rec!{ (match $scrutinee {
            $first_pat $(if $first_guard)? => $first_body,
            $($($pat $(if $guard)? => break $label,)?)*
        }), $($label $(: ($body))?),* }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! fallthrough_rec {
    (($($acc:tt)*),) => {$($acc)*};
    (($($acc:tt)*), $label:lifetime) => {
        $label: {
            $($acc)*
        }
    };
    (($($acc:tt)*), $label:lifetime: ($($body:tt)*) $(,$($follow:tt)*)? ) => {

        $crate::fallthrough_rec!{($label: {
                $($acc)*
            }
            $($body)*
        ), $($($follow)*)?}
    };
}

//

// Source: https://gitlab.com/okannen/likely/-/blob/577e7ac62dbeddf573ba6b9f5ad46e185c1b8336/src/lib.rs
//
// Copyright 2021 Olivier Kannengieser
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

/// Brings [likely](core::intrinsics::likely) to stable rust.
#[inline(always)]
pub const fn likely(b: bool) -> bool {
    #[allow(clippy::needless_bool)]
    if (1i32).checked_div(if b { 1 } else { 0 }).is_some() {
        true
    } else {
        false
    }
}

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}
