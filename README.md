<!---
-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
---> 

## rust-lean-models

Lean models of various functions and data types from Rust libraries to facilitate Lean-based verification of Rust programs.


## Description
This library is intended to be used for verifying Rust programs via Lean. It
defines equivalent Lean versions of functions from the Rust standard library.

The Lean definitions are based on the description of the Rust functions, which is published at https://doc.rust-lang.org/std.

The library includes:
- Definitions of Lean functions equivalent to those from the Rust standard library
- Proofs that these definitions are consistent with the description of the Rust functions
- Supporting lemmas and theorems for proof construction

## Installation

-  Add the following lines to your `lakefile.lean`:

    ` require «rust-lean-models» from git "https://github.com/model-checking/rust-lean-models" `

- Change the lean version in your `lean-toolchain` to the one in 
[lean-toolchain](https://github.com/model-checking/rust-lean-models/blob/main/lean-toolchain)

- Run `lake update` in the terminal.

- Import the packages and open the namespaces in your Lean files 
(see [ProofTutorial.lean](https://github.com/model-checking/rust-lean-models/tree/main/RustLeanModels/ProofTutorial.lean))

    ```lean
    import RustLeanModels.Basic
    import RustLeanModels.RustString
    open RustString
    open Iterator
    ```

## Usage
### Translating a Rust program 

Replace the Rust built-in functions that are used in your code with the
corresponding Lean function in this library.

Tables in [RustString.md](RustLeanModels/RustString.md)
and [Iterators.md](RustLeanModels/Iterator.md) give the mapping from Rust types
and functions to their Lean equivalents.

### Proof Tutorial

We demonstrate the applications of the library and some proof techniques 
for string programs in
[ProofTutorial.lean](https://github.com/model-checking/rust-lean-models/tree/main/RustLeanModels/ProofTutorial.lean).
This tutorial shows the correctness of two simple programs that compute the longest common prefix
and longest common substring of the two strings.
More examples can be found in 
[ProofExample.lean](https://github.com/model-checking/rust-lean-models/tree/main/RustLeanModels/ProofExample.lean).

## Details

### Recursive function definitions

For each Rust function, we provide a recursive Lean function. Implementing 
the equivalent functions in Lean recursively enables users to construct
induction proofs conveniently. The Lean function has the same name as the Rust original, 
except when the Rust name clashes with a Lean keyword. In case of a clash, a Rust function `func_name`
is renamed to `rust_func_name` in Lean.

Implementing a function recursively may requires some extra parameters.
In those cases, we first define an auxiliary function (name: `func_name_aux`) which is defined
recursively with the extra parameters, then we define the function `func_name` based on the auxiliary function
with initial values for the parameters.
For example, `char_indices` is defined based on `char_indices_aux` as 
```lean
def char_indices (s: Str) := char_indices_aux s 0
```

For Rust functions that use the Rust `Pattern` type, we implement two recursive sub-functions
(name: `func_name_char_filter` and  `func_name_substring`) that replace the `Pattern` type
in the input with either a char filter (of type`Char → Bool`) or a string (of type `List Char`).
Then we define the function `func_name` based on these two sub-functions by matching the
input of `Pattern` type. For example, `split` is defined by two sub-functions
`split_char_filter` and `split_substring` as:

```lean
def split (s: Str) (p: Pattern) := match p with
| Pattern.SingleChar c => split_char_filter s (fun x => x = c)
| Pattern.ListChar l => split_char_filter s (fun x => x ∈ l)
| Pattern.FilterFunction f => split_char_filter s f
| Pattern.WholeString s1 => split_substring s s1
```

All recursive implementations are proven to be "correct" in the sense that
they are consistent with the descriptions of the Rust versions (see below for more details).

## Correctness Proofs

### For functions that return `Bool` or can be defined based on other functions that have already been proven correct
   
- First, we provide a variant Lean definition of the Rust function that we call the definitional 
version (with name `func_name_def`).  This version is intended to match the documented description 
of the Rust function. Ideally, the definitional version should not contain recursion, except in some trivial cases, 
but it can make use of the recursive versions of other functions that have been previously proven correct.

- Then, we state and prove a theorem that shows that the recursive and definitional versions of Rust 
function `func_name` are equivalent. This equivalence theorem is called `func_name_EQ` and 
it has type `func_name = func_name_def`.
The theorem ensures that the function is implemented correctly 
and allows the two versions to be used interchangeably. 
In some cases, constructing a non-induction proof using the definitional version is more convenient.

- For example, the function `is_char_boundary` has a definitional version: 

    ```lean
    def is_char_boundary_def (s: Str) (i: Nat) := i ∈ ListCharPos s ∨  i = byteSize s
    ```

    a recursive definition:

    ```lean
    def is_char_boundary (s: Str) (i: Nat) := match s with
    | [] => i == 0
    | h::t => if i = 0 then true else
        if i < Char.utf8Size h then false else is_char_boundary t (i - Char.utf8Size h)
    ```

    and an equivalence theorem 
    
    ```lean
    theorem is_char_boundary_EQ : is_char_boundary s p =  is_char_boundary_def s p
    ```

When the description of a Rust function cannot be efficiently expressed in Lean (requires recursions, or is unintuitive),
we can:
- Define the definitional version (similar to Case 1) based on a recursive trivial function, then prove the equivalence theorem.
For example, the `byteSize_def` function is based on the function `sum_list_Nat`
that computes the sum of a list of natural numbers:
    
    ```lean
    def sum_list_Nat (l : List Nat) := List.foldl Nat.add 0 l`
    def byteSize_def (s : List Char) : Nat := sum_list_Nat (List.map (fun x: Char => Char.utf8Size x) s)
    ```

- Define and prove the correctness of one/some subordinate function(s), 
then define the definitional version based on them. 
    For example, to define `split_inclusive_char_filter_def`, we first define and prove the correctness of two functions:
    - `list_char_filter_charIndex (s: Str) (f: Char → Bool)`: returns the list of positions of characters in `s` satisfying the filter `f`

    - `split_at_charIndex_list (s: Str) (l: List Nat)`: splits the strings `s` at positions in `l`

    then we define `split_inclusive_char_filter_def` as follows:

    ```lean
    def split_inclusive_char_filter_def (s: Str) (f: Char → Bool) :=
        split_at_charIndex_list s (List.map (fun x => x+1) (list_char_filter_charIndex s f))
    ```

### When the Rust documentation describes properties of the return value

We state and prove a soundness theorem for the function with
name: `func_name_sound` and type: `x = func_name input1 input2 ...  ↔ properties of x`.

For example, the soundness theorem for the function `floor_char_boundary` defined as:

```lean
def floor_char_boundary_aux (s: Str) (i: Nat) (k: Nat): Nat := match s with
  | [] => k
  | h::t => if i < Char.utf8Size h then k else floor_char_boundary_aux t (i - Char.utf8Size h) (k + Char.utf8Size h)

def floor_char_boundary (s: Str) (i: Nat) := floor_char_boundary_aux s i 0
```

is

```lean
theorem floor_char_boundary_sound:  flp = floor_char_boundary s p
      ↔ (is_char_boundary s flp) ∧ (flp ≤ p) ∧ (∀ k, ((is_char_boundary s k) ∧ (k ≤ p)) → k ≤ flp )
```

- The soundness theorem should cover all the properties in the Rust documentation.
- We make some minor/trivial adjustments when needed to express the properties in Lean.
- The modus ponens (→) direction of the theorem is enough to ensure the correctness of the recursive version
if the properties in the right-hand-side ensure that the function in the left-hand-side is deterministic.
- The modus ponens reverse (←) direction ensures that we stated enough properties in right-hand-side such that 
it can be satisfied by only one function.

If the function returns an option, we separately state and prove two soundness theorems for the two cases
of the return value: `func_name_none_sound` and `func_name_some_sound`. For example:
    
    ```lean
    theorem split_at_none_sound : split_at s p = none ↔ ¬ ∃ s1, List.IsPrefix s1 s ∧ byteSize s1 = p
    theorem split_at_some_sound : split_at s p = some (s1, s2) ↔ byteSize s1 = p ∧ s = s1 ++ s2
    ```

For functions involving the `Pattern` type,  we separately state and prove two equivalent/soundness
theorems for the two sub-functions discussed previously (`func_name_char_filter_EQ` and `func_name_substring_EQ`) 
or (`func_name_char_filter_sound` and `func_name_substring_sound`). For example:
    
    ```lean
    theorem contains_char_filter_EQ : contains_char_filter s f  = contains_char_filter_def s f
    theorem contains_substring_EQ : contains_substring s p  = contains_substring_def s p
    ```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
