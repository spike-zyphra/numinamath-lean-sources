import Mathlib

theorem algebra_288541 (a : ℝ) (h : ∃! x : ℝ, x^2 + a * abs x + a^2 - 3 = 0) :
    a = Real.sqrt 3 := by
  rcases h with ⟨x₀, h₀, h₁⟩
  have heq1 : (-x₀) ^ 2 + a * abs (-x₀) + a^2 - 3 = 0 := by
    have h_eq : x₀ ^ 2 + a * abs x₀ + a^2 - 3 = 0 := h₀
    have h_eq2 : abs (-x₀) = abs x₀ := by 
      simp [abs_neg]
    rw [h_eq2]
    nlinarith
  have hx₀ : x₀ = 0 := by
    have h_eq : (-x₀) ^ 2 + a * abs (-x₀) + a^2 - 3 = 0 := heq1
    have h_eq2 : (-x₀) = x₀ := by 
      apply h₁ 
      exact_mod_cast h_eq 
    nlinarith 
  rw [hx₀] at h₀ 
  have ha2 : a^2 = 3 := by 
    norm_num [abs_zero] at h₀ 
    nlinarith 
  have ha3 : a ≥ 0 := by
    by_contra h
    push_neg at h
    have h2 : a < 0 := h 
    -- Let's prove existence of sqrt 3.
    have h2 : (Real.sqrt 3) ^ 2 + a * abs (Real.sqrt 3) + a^2 - 3 = 0 := by 
      rw [show abs (Real.sqrt 3) = Real.sqrt 3 by 
        simp [abs_of_nonneg, show 0 ≤ (Real.sqrt 3 : ℝ) by positivity]
      ]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h3 : Real.sqrt 3 = x₀ := by 
      apply h₁ 
      exact_mod_cast h2
    have h4 : Real.sqrt 3 = 0 := by 
      nlinarith [h3, hx₀]
    have h5 : Real.sqrt 3 > 0 := by 
      positivity 
    linarith 
  have h2 : a = Real.sqrt 3 := by 
    have h4 : a^2 = 3 := ha2 
    have h5 : a ≥ 0 := ha3 
    have h6 : a = Real.sqrt 3 := by 
      have h7 : a^2 = 3 := h4 
      have h8 : a ≥ 0 := h5 
      have h10 : a = Real.sqrt 3 := by 
        rw [←h7]
        field_simp 
      linarith 
    linarith 
  exact_mod_cast h2