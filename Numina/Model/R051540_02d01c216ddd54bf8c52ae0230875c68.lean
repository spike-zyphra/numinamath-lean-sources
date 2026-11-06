import Mathlib

theorem algebra_22246 (k : ℝ) (h : ∃ m, (19 - 9) * m = k - 1 ∧ (7 - 9) * m = 0 - 1) :
    k = 6 := by
  rcases h with ⟨m, hm1, hm2⟩
  have hm : m = 1 / 2 := by 
    linarith
  rw [hm] at hm1
  linarith