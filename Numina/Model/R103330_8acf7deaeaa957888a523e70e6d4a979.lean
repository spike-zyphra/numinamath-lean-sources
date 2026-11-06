import Mathlib

theorem algebra_291018 : (X^95 + ∑ i ∈ Finset.range 95, X^i) % (X^31 + ∑ i ∈ Finset.range 31, X^i) = 0 := by
  have h1 : X^95 + ∑ i in Finset.range 95, X^i = (X^31 + ∑ i in Finset.range 31, X^i) * (X^64 + X^32 + 1) := by 
    simp only [Finset.sum_range_succ]
    ring
  rw [h1]
  simp