import Mathlib

theorem number_theory_145869 (n : ℕ) (h : ∑ i ∈ Finset.range 9, (n + i) = 43040102 - (n % 10)) :
    n / 10 = 8 := by
  have h1 : ∑ i in Finset.range 9, (n + i) = 9 * n + 36 := by
    simp [Finset.sum_range_succ]
    <;> ring_nf
    <;> omega
  rw [h1] at h
  omega