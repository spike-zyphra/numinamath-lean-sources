import Mathlib

open Real

theorem algebra_19590 {g t : ℝ → ℝ} (hg : g = fun x => sqrt x) (ht : t = fun x => 3 - g x) :
    t (g 16) = 1 := by
  have g16 : g 16 = sqrt 16 := by
    rw [hg]
  have g16_val : g 16 = 4 := by
    rw [g16]
    have h1 : sqrt (16 : ℝ) = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h1
  have g4_val : g 4 = 2 := by 
    rw [hg]
    have h2 : sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp [h2]
 
  rw [ht]
  simp [g16_val, g4_val]
  all_goals norm_num