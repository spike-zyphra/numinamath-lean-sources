import Mathlib

open Real Set
open scoped Real

theorem calculus_16591 {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) (h : sin x = (1 + sqrt 5) / 2) :
    x = π / 4 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [hx1, hx2, Real.pi_pos]
    linarith [hx1, hx2, Real.pi_pos]
  have h2 : sin x < 1 := by 
    have h3 : sin x < sin (Real.pi / 2) := by 
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals 
        linarith [hx1, hx2, Real.pi_pos]
    have h4 : sin (Real.pi / 2) = 1 := by 
      rw [sin_pi_div_two]
    linarith [h3, h4]
  nlinarith [h, h1, h2, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]