<!---
-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
---> 
## Rust String 

## Data type conversion
- String is converted to `List Char` in Lean. This helps constructing induction proofs.
- The integer types that are used in String indexing are converted to `Nat` in the Lean implementation.
This assumes that overflow exceptions will not happen. Note that overflow exceptions can only happen 
in Rust programs which use usize for String indexing when the Strings size are GBs.
- Byte Lists (for UTF8 conversion) are represented as `List Nat` in Lean. Strings are converted from `List Char` to `List Nat` by the function `Str_toUTF8`. 
  This function ensures that the output is a valid UTF8 string. We use three axioms: `Char_Pos0`, `Char_Diff`, and `Char_Size` which describe
  the properties of UTF8 encoding (see UTF8Str.lean).
- The trait std::str::pattern::Pattern is converted to the inductive type `Pattern` (see RustString.lean).



## Implemented functions in RustString
| Rust String function                 | Equivalent Lean function       | Description link |
| ----------------------------- | ------------------- | ---------------------- |
| core::str::bytes |   UTF8Str.Str_toUTF8    | https://doc.rust-lang.org/std/primitive.str.html#method.bytes |
| core::str::ceil_char_boundary |   ceil_char_boundary    | https://doc.rust-lang.org/std/primitive.str.html#method.ceil_char_boundary |
| core::str::char_indices |   char_indices    | https://doc.rust-lang.org/std/primitive.str.html#method.char_indices |
| core::str::contains |   contains    | https://doc.rust-lang.org/std/primitive.str.html#method.contains |
| core::str::ends_with |   ends_with    | https://doc.rust-lang.org/std/primitive.str.html#method.ends_with |
| core::str::eq_ignore_ascii_case |   eq_ignore_ascii_case    | https://doc.rust-lang.org/std/primitive.str.html#method.eq_ignore_ascii_case |
| core::str::find |   find    | https://doc.rust-lang.org/std/primitive.str.html#method.find |
| core::str::get |   string_slice    | https://doc.rust-lang.org/std/primitive.str.html#method.get |
| core::str::is_ascii |   is_ascii    | https://doc.rust-lang.org/std/primitive.str.html#method.is_ascii |
| core::str::is_char_boundary |   is_char_boundary    | https://doc.rust-lang.org/std/primitive.str.html#method.is_char_boundary |
| core::str::lines |   lines    | https://doc.rust-lang.org/std/primitive.str.html#method.lines |
| core::str::match_indices |   match_indices    | https://doc.rust-lang.org/std/primitive.str.html#method.match_indices |
| core::str::matches |   rust_matches    | https://doc.rust-lang.org/std/primitive.str.html#method.matches |
| core::str::repeat |   rust_repeat    | https://doc.rust-lang.org/std/primitive.str.html#method.repeat |
| core::str::replace |   replace    | https://doc.rust-lang.org/std/primitive.str.html#method.replace |
| core::str::replacen |   replacen    | https://doc.rust-lang.org/std/primitive.str.html#method.replacen |
| core::str::rfind |   rfind    | https://doc.rust-lang.org/std/primitive.str.html#method.rfind |
| core::str::rmatch_indices |   rmatch_indices    | https://doc.rust-lang.org/std/primitive.str.html#method.rmatch_indices |
| core::str::rsplit |   rsplit    | https://doc.rust-lang.org/std/primitive.str.html#method.rsplit |
| core::str::rsplit_once |   rsplit_once    | https://doc.rust-lang.org/std/primitive.str.html#method.rsplit_once |
| core::str::rsplit_terminator |   rsplit_terminator    | https://doc.rust-lang.org/std/primitive.str.html#method.rsplit_terminator |
| core::str::split |   split    | https://doc.rust-lang.org/std/primitive.str.html#method.split |
| core::str::split_ascii_whitespace |   split_ascii_whitespace    | https://doc.rust-lang.org/std/primitive.str.html#method.split_ascii_whitespace |
| core::str::split_at |   split_at_checked    | https://doc.rust-lang.org/std/primitive.str.html#method.split_at |
| core::str::split_inclusive |   split_inclusive    | https://doc.rust-lang.org/std/primitive.str.html#method.split_inclusive |
| core::str::split_once |   split_once    | https://doc.rust-lang.org/std/primitive.str.html#method.split_once |
| core::str::split_terminator |   split_terminator    | https://doc.rust-lang.org/std/primitive.str.html#method.split_terminator |
| core::str::split_whitespace |   split_whitespace    | https://doc.rust-lang.org/std/primitive.str.html#method.split_whitespace |
| core::str::splitn |   splitn    | https://doc.rust-lang.org/std/primitive.str.html#method.splitn |
| core::str::starts_with |   starts_with    | https://doc.rust-lang.org/std/primitive.str.html#method.starts_with |
| core::str::strip_prefix |   strip_prefix    | https://doc.rust-lang.org/std/primitive.str.html#method.strip_prefix |
| core::str::strip_suffix |   strip_suffix    | https://doc.rust-lang.org/std/primitive.str.html#method.strip_suffix |
| core::str::to_ascii_lowercase |    to_ascii_lowercase    | https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_lowercase |
| core::str::to_ascii_uppercase |   to_ascii_uppercase    | https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_uppercase |
| core::str::to_lowercase |   not yet   | https://doc.rust-lang.org/std/primitive.str.html#method.to_lowercase |
| core::str::to_uppercase |   not yet    | https://doc.rust-lang.org/std/primitive.str.html#method.to_uppercase |
| core::str::trim |   trim    | https://doc.rust-lang.org/std/primitive.str.html#method.trim |
| core::str::trim_ascii |   trim_ascii    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii |
| core::str::trim_ascii_end |   trim_ascii_end   | https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_end |
| core::str::trim_ascii_start |   trim_ascii_start    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_start |
| core::str::trim_end |   trim_end    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_end |
| core::str::trim_end_matches |   trim_end_matches    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_end_matches |
| core::str::trim_matches |   trim_matches    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_matches |
| core::str::trim_start |   trim_start    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_start |
| core::str::trim_start_matches |   trim_start_matches    | https://doc.rust-lang.org/std/primitive.str.html#method.trim_start_matches |



## Implemented functions in Lean library for List
| Rust String function                 | Lean equivalent function       | Description link |
| ----------------------------- | ------------------- | ---------------------- |
| core::str::chars |   <em>self    | https://doc.rust-lang.org/std/primitive.str.html#method.chars |
| core::str::is_empty |   List.isEmpty    | https://doc.rust-lang.org/std/primitive.str.html#method.is_empty |
| core::str::len |   List.length    | https://doc.rust-lang.org/std/primitive.str.html#method.len |

## Limitations
The RustString library does not include:
- Functions that mutate their input (e.g., make_ascii_lowercase), but it includes the cloning version (e.g. to_ascii_lowercase).
- Functions which may panic (e.g., slice indexing), but it includes the non-panicking version (e.g. `str::get`)