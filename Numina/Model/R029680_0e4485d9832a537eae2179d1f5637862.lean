import Mathlib

theorem algebra_5284 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^3 - 12 * x^2 + a * x + b)
    (h₀ : ∀ x y, x < y → f x < f y) (h₁ : f (f (f 3)) = 3) (h₂ : f (f (f (f 4))) = 4) :
    f 7 = 31 := by 
  have h3 : f 3 ≥ 3 := by
    by_contra h
    push_neg at h
    have h4 : f (f 3) < f 3 := by
      apply h₀
      all_goals linarith
    have h5 : f (f (f 3)) < f (f 3) := by
      apply h₀
      all_goals linarith
    have h6 : f (f (f 3)) < f 3 := by
      linarith
    nlinarith [show f (f (f 3)) = 3 by linarith [h₁], h6]
  have h4 : f 4 ≥ 4 := by
    by_contra h
    push_neg at h
    have h5 : f (f 4) < f 4 := by
      apply h₀
      all_goals linarith
    have h6 : f (f (f 4)) < f (f 4) := by
      apply h₀
      all_goals linarith
    have h7 : f (f (f (f 4))) < f (f (f 4)) := by
      apply h₀
      all_goals linarith
    have h8 : f (f (f (f 4))) < f 4 := by
      linarith
    nlinarith [show f (f (f (f 4))) = 4 by linarith [h₂], h8]
  have h5 : f 3 ≤ 3 := by
    by_contra h
    push_neg at h
    have h6 : f (f 3) > f 3 := by
      apply h₀
      all_goals linarith
    have h7 : f (f (f 3)) > f (f 3) := by
      apply h₀
      all_goals linarith
    nlinarith [show f (f (f 3)) = 3 by linarith [h₁], h7]
  have h6 : f 3 = 3 := by
    linarith
  have h7 : f 4 ≤ 4 := by
    by_contra h
    push_neg at h
    have h8 : f (f 4) > f 4 := by
      apply h₀
      all_goals linarith
    have h9 : f (f (f 4)) > f (f 4) := by
      apply h₀
      all_goals linarith
    have h10 : f (f (f (f 4))) > f (f (f 4)) := by
      apply h₀
      all_goals linarith
    have h11 : f (f (f (f 4))) > f 4 := by
      linarith
    nlinarith [show f (f (f (f 4))) = 4 by linarith [h₂], h11]
  have h8 : f 4 = 4 := by
    linarith
  have eq3 : (3:ℝ)^3 - 12 * (3:ℝ)^2 + a * 3 + b = 3 := by
    rw [hf] at h6
    simpa using h6
  have eq4 : (4:ℝ)^3 - 12 * (4:ℝ)^2 + a * 4 + b = 4 := by
    rw [hf] at h8
    simpa using h8
  have ha : a = 48 := by 
    linarith 
  have hb : b = -60 := by
    linarith 
  have h9 : f 7 = 31 := by
    rw [hf]
    simp [ha, hb]
    norm_num
  exact h9