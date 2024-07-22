<!---
-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
---> 

## rust-lean-models

Lean models of various Rust libraries to facilitate Lean-based verification of Rust programs.


## Description
The library defines equivalent Lean versions of functions from the Rust standard library.
This library is intended to be used for verifying Rust programs via Lean.

The Lean implementation is based on the description of the Rust functions, which are published at https://doc.rust-lang.org/std.
The library includes:
- Definitions of functions equivalent to those from the Rust standard library
- Proofs that these definitions are consistent with the description of the Rust functions
- Supporting lemmas and theorems for proof construction

## Installation

To use the library, add the following lines to your `lakefile.lean`:

` require rust-lean-models from git "https://github.com/model-checking/rust-lean-models" `

Then do `lake update` in the terminal.

## Usage
### Translating a Rust program 

For any Rust built-in functions which are used in user code , map it with 
the corresponding function name in the library (see the Tables below).

### Proof Tutorial
We demonstrate some proof techniques in Proof_Tutorial.lean through two simple programs that compute
the longest common prefix and longest common substring of the two input strings. 
More examples can be found in Proof_Example.lean

## Implementation


### Recursive function definition
For each Rust function, we provide a recursive Lean function. Implementing 
the equivalent functions in Lean recursively enables user to construct 
induction proofs conveniently. The Lean function has the same as the Rust original, 
except when the Rust name  clashes with a Lean keyword. In case of a clash, a Rust function 'func_name' 
is renamed to `rust_func_name` in Lean.

Implementing a function recursively may requires some extra parameters.
In those cases, first, we implement an auxiliary function (name: `func_name_aux`) which is defined 
recursively with the parameters, then we define the function `func_name` based on the auxiliary function 
with initial values for the parameters. 
For example, `char_indices` is defined based on `char_indices_aux` as 
`def char_indices (s: Str):= char_indices_aux s 0`.

For Rust functions involving the `Pattern` type, we implement two recursive sub-functions 
(name: `func_name_char_filter` and  `func_name_substring`) which replace the `Pattern` type 
in the input by either a char filter (or type`Char → Bool`) or a `List Char`. Then we define 
the function `func_name` based on these two sub-functions by matching the input of `Pattern` type.
For example, `split` is defined by two sub-functions `split_char_filter` and `split_substring` as: 

```
def split (s: Str) (p: Pattern) := match p with
| Pattern.SingleChar c => split_char_filter s (fun x => x = c)
| Pattern.ListChar l => split_char_filter s (fun x => x ∈ l)
| Pattern.FilterFunction f => split_char_filter s f
| Pattern.WholeString s1 => split_substring s s1
```
All recursive implementations are proven to be "correct" in the sense that they are consistent with
the Rust original (see below for more details).

## Correctness Proofs

### For functions that return Bool or can be defined based on other functions that have already been proven correct
   
- First, we provide a variant Lean definition of the Rust function that we call the definitional 
version (with name`func_name_def`).  This version is intended to match the documented description 
of the Rust function. Ideally, the definitional version should not contains recursion, except in some trivial cases, 
but it can make use of the recursive versions of other functions that have been previously proven correct.

- Then, we state and prove a theorem that shows that the recursive and definitional versions of Rust 
function `func_name` are equivalent. This equivalence theorem is called `func_name_EQ` and 
it has type `func_name = func_name_def`.
The theorem ensures that the function is implemented correctly 
and allows the two versions to be used interchangably. 
In some cases, constructing a non-induction proof using the definitional version is more convenient.

- For example, the function `is_char_boundary` has a definitional version: 

    `def is_char_boundary_def (s: Str) (p: Nat) := p ∈ (ListCharPos s ++ [byteSize s])`

    and an equivalence theorem 

    `theorem is_char_boundary_EQ : is_char_boundary s p =  is_char_boundary_def s p`.

When Rust description cannot be efficiently expressed in Lean (require recursions, or very unintuitive),
we can:
- Define the definitional version (similar to Case 1) based on a recursive trivial function, then prove the equivalence theorem.
For example, the `byteSize_def` function is defined on the simple function `sum_list_Nat`
that computes the sum of a list of natural numbers:
    
    ```
    def sum_list_Nat (l : List Nat) := List.foldl Nat.add 0 l`
    def byteSize_def (s : List Char) : Nat := sum_list_Nat (List.map (fun x: Char => Char.utf8Size x) s)
    ```

- Define and prove the correctness of one/some subordinate function(s), 
then define the definitional version based on them. 
    For example, to define `split_inclusive_char_filter_def`, firstly we define and prove the coreectness of two functions:
    - `list_char_filter_charpos (s: Str) (f: Char → Bool)`: returns the list of positions of characters in `s` satisfying the filter `f`

    - `split_at_charpos_list (s: Str) (l: List Nat)`: split the strings `s` at positions in `l`

    then define `split_inclusive_char_filter_def` based on them:

    ```
    def split_inclusive_char_filter_def (s: Str) (f: Char → Bool):= split_at_charpos_list s (List.map (fun x => x+1) (list_char_filter_charpos s f))
    ```
defined based on the
### When the Rust documentation describes properties of the return value 
We state and prove a soundness theorem for the function with
name: `func_name_sound` and type: `x = func_name input1 input2 ...  ↔ properties of x`.
For example, the soundness thorem for the function `floor_char_boundary` is 

```
theorem floor_char_boundary_sound:  flp = floor_char_boundary s p
      ↔ (is_char_boundary s flp) ∧ (flp ≤ p) ∧ (∀ k, ((is_char_boundary s k) ∧ (k ≤ p)) → k ≤ flp )
```

- The soundness theorem should cover all the properties in the Rust documentation.
- We make some minor/trivial adjustments when needed to express the properties in Lean.
- The modus ponens (→) direction of the theorem is enough to ensure the correctness of the recursive version
if the properties in the right-hand-side ensure that the function in the left-hand-side is deterministic.
- The modus ponens reverse (←) direction ensures that we stated enough properties in right-hand-side such that 
it can be satisfied by only one function. 
- If the function returns an option, we separately state and prove two soundness theorems for the two cases 
of the return value: `func_name_none_sound` and `func_name_some_sound`. For example:

    `theorem split_at_none_sound : split_at s p = none ↔ ¬ ∃ s1, List.IsPrefix s1 s ∧ byteSize s1 = p`

    `theorem split_at_some_sound : split_at s p = some (s1, s2) ↔ byteSize s1 = p ∧ s = s1 ++ s2`

- For functions involving the `Pattern` type,  we separately state and prove two equivalent/soundness 
theorems for the two sub-functions discussed previously (`func_name_char_filter_EQ` and `func_name_substring_EQ`) 
or (`func_name_char_filter_sound` and `func_name_substring_sound`). For example:
    
    `theorem contains_char_filter_EQ : contains_char_filter s f  = contains_char_filter_def s f `

    `theorem contains_substring_EQ : contains_substring s p  = contains_substring_def s p`

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
