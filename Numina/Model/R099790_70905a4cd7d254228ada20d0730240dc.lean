import Mathlib

theorem algebra_15197 (a b c : ℝ) (h₀ : a = 8) (h₁ : b = 15) (h₂ : c = 17) :
    (1/2) * a * b * Real.sin (Real.arccos ((a^2 + b^2 - c^2)/(2*a*b))) = 60 := by
  rw [h₀, h₁, h₂]
  have h3 : (8^2 + 15^2 - 17^2 : ℝ) = 0 := by norm_num
  have h4 : ((8^2 + 15^2 - 17^2) / (2 * (8 : ℝ) * (15 : ℝ))) = 0 := by
    rw [show (8^2 + 15^2 - 17^2 : ℝ) = 0 by linarith]
    norm_num
  have h5 : Real.sin (Real.arccos ((8^2 + 15^2 - 17^2) / (2 * (8 : ℝ) * (15 : ℝ)))) = 1 := by
    rw [h4]
    have h : Real.sin (Real.arccos (0 : ℝ)) = 1 := by
      have h1 : Real.arccos (0 : ℝ) = Real.pi / 2 := by
        have h2 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
        rw [← h2]
        apply Real.arccos_cos
        all_goals linarith [Real.pi_pos]
      rw [h1]
      exact Real.sin_pi_div_two
    exact h
  rw [h5]
  norm_num