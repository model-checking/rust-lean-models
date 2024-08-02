<!---
-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
---> 
## Rust Iterator 

## Data type conversion
- The `Iterator` trait is converted to `List` in Lean. Many functions defined in Lean's core are
equivalent to Rust functions that operate on iterators.


## Functions implemented in Iterator.lean

| Rust Iterator function                 | Lean equivalent function       | Description link |
| ----------------------------- | ------------------- | ---------------------- |
| std::iter::Iterator::flatten |   flatten    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.flatten |
| std::iter::Iterator::next |   next    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.next |
| std::iter::Iterator::peek |   peek    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.peek |

## Functions already defined in Lean

| Rust Iterator function                 | Lean equivalent function       | Description link |
| ----------------------------- | ------------------- | ---------------------- |
| std::iter::Iterator::all |   List.all    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.all |
| std::iter::Iterator::any |   List.any    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.any |
| std::iter::Iterator::chain |   List.append    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.chain |
| std::iter::Iterator::collect |   <em>self    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.collect |
| std::iter::Iterator::count |   List.length    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.count |
| std::iter::Iterator::emunerate |   List.enum    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.enumerate |
| std::iter::Iterator::fold |   List.foldl    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.fold |
| std::iter::Iterator::last |   List.getLast    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.last |
| std::iter::Iterator::map |   List.map    | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.map |
| std::iter::Iterator::nth |   List.get?   | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.nth |
| std::iter::Iterator::position |   List.findSome?   | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.position |
| std::iter::Iterator::rev |   List.reverse   | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.rev |
| std::iter::Iterator::unzip |   List.unzip   | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.unzip |
| std::iter::Iterator::zip |   List.zip   | https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.zip |

