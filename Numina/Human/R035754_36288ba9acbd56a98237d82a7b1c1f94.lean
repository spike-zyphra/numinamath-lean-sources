import Mathlib

/-Each term of a sequence, after the first term, is inversely proportional to the term preceding it, and the constant of proportionality stays the same. If the first term is 2 and the second term is 5, what is the 12th term?-/
theorem algebra_611039 :
    ∏ i ∈ Finset.range 351, (i ^ 3 - (350 - i) : ℤ) = 0 := by
  -- 0 . One of the factors is $7^{3}-343=0$, so the whole product is zero.
  rw [Finset.prod_eq_zero_iff]
  use 7
  norm_num