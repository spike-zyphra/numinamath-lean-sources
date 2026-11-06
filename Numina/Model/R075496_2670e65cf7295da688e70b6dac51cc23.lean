import Mathlib

theorem number_theory_252343 (n : ℤ) (h : ∑ i ∈ Finset.range 1259, (n + i) = 1259) :
    n + 1258 = 630 := by

  have h1 : ∑ i in Finset.range 1259, (n + i) = 1259 * n + ∑ i in Finset.range 1259, (i : ℤ) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_range]
    <;> ring

  have h2 : ∑ i in Finset.range 1259, (i : ℤ) = (1258 * 1259) / 2 := by 
    native_decide

  rw [h1, h2] at h

  -- Solve equation to find n
  omega