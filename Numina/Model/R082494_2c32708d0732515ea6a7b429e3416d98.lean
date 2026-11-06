import Mathlib

theorem algebra_147204 (x : ℕ) (hx : x ≥ 63) (h : ∑ i ∈ Finset.range 31, (x + i) = 1994) :
    x = 30 ∨ x = 28 := by
  have h1 : ∑ i in Finset.range 31, (x + i) = 31 * x + 465 := by
    simp only [Finset.sum_range_succ]
    ring_nf
    <;> omega
  rw [h1] at h
  omega