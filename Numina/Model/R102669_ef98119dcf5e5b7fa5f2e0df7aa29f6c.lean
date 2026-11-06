import Mathlib

theorem number_theory_213535 (K : ℝ → ℝ) (hK : K = fun x => x / 24) :
    K 24 = 1 ∧ K 12 = 50 / 100 := by 
  constructor
  · -- Show K 24 = 1
    rw [hK]
    norm_num
  · -- Show K 12 = 50 / 100
    rw [hK]
    norm_num