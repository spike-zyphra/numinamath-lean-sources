import Mathlib

/- Show that the product of two integers of the form \(6k + 5\) is of the form \(6m + 1\) for some integer \(m\).-/
theorem number_theory_4997 (k1 k2 : ℤ) :
    ∃ m, (6 * k1 + 5) * (6 * k2 + 5) = 6 * m + 1 := by
  --we prove that the product of two integers of the form 6k+5 is of the form 6k+1
  use (6 * k1 * k2 + 5 * k1 + 5 * k2 + 4); ring
