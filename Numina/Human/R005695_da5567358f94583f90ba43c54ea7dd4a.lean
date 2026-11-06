import Mathlib

/-!
We want to compute the number of rotationally distinct colorings of a 2x2 square grid
where each square can be painted with one of `n` colors (n = 10).

Rotational equivalence includes 0°, 90°, 180°, 270° rotations.

Using Burnside's lemma:

- 0° rotation (identity): all `n^4` colorings are fixed
- 180° rotation: swaps opposite corners → fixed if (1=3 and 2=4) ⇒ `n^2` fixed colorings
- 90° and 270° rotation: all four must be same color ⇒ `n` fixed colorings

So the number of distinct colorings is:

  (n⁴ + n² + 2n) / 4

For n = 10, this equals 2530.
-/

def distinctColorings (n : ℕ) : ℕ :=
  (n ^ 4 + n ^ 2 + 2 * n) / 4

#eval distinctColorings 10  -- Expect 2530

theorem Combinatorics_609461 : distinctColorings 10 = 2530 := by
  norm_num [distinctColorings]
