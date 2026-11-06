import Mathlib

theorem algebra_167956 (f : ℝ → ℝ) (h : ∀ x y, f x * f y = f (x - y)) :
    f 2017 = 0 ∨ f 2017 = 1 := by 
  have h0 : f 0 * f 0 = f 0 := by
    specialize h 0 0
    norm_num at h
    linarith
  have hfx_sq : ∀ x, f x ^ 2 = f 0 := by
    intro x 
    have h1 := h x x
    norm_num at h1
    nlinarith
  have h0_eq : f 0 = 0 ∨ f 0 = 1 := by 
    have h1 : f 0 * (f 0 - 1) = 0 := by linarith [h0]
    cases (mul_eq_zero.mp h1) with
    | inl h0 => left; linarith 
    | inr h0 => right; linarith 
  cases h0_eq with
  | inl h0_eq_0 =>
    have h_all_zero : ∀ x, f x = 0 := by
      intro x 
      have h1 := hfx_sq x 
      rw [h0_eq_0] at h1
      have : f x ^ 2 = 0 := by linarith 
      simp at this 
      exact this 
    have h2017_zero : f 2017 = 0 := h_all_zero 2017 
    left 
    exact h2017_zero
  | inr h0_eq_1 =>
    have h2017_sq : f 2017 ^ 2 = 1 := by 
      specialize hfx_sq 2017 
      rw [h0_eq_1] at hfx_sq 
      linarith 
    have h_subst : f 2017 * f (2017 / 2) = f (2017 / 2) := by 
      specialize h 2017 (2017 / 2) 
      norm_num at h 
      linarith
    have h2017_eq_1 : f 2017 = 1 := by
      have h2017_div_2_sq : f (2017 / 2) ^ 2 = 1 := by
        specialize hfx_sq (2017 / 2) 
        rw [h0_eq_1] at hfx_sq 
        linarith
      have h2017_div_2_ne_zero : f (2017 / 2) ≠ 0 := by
        by_contra h_eq_zero
        rw [h_eq_zero] at h2017_div_2_sq 
        nlinarith
      have h_eq : (f 2017 - 1) * f (2017 / 2) = 0 := by 
        linarith [h_subst]
      cases (mul_eq_zero.mp h_eq) with
      | inl h_eq1 => 
        linarith 
      | inr h_eq2 => 
        exfalso 
        apply h2017_div_2_ne_zero 
        linarith 
    right 
    linarith [h2017_eq_1]