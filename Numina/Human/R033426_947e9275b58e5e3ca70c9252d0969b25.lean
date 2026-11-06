import Mathlib
/-let f: ℝ → ℝ be a function satisfying f(x)f(y)=f(x-y). Find all possible values of f(2017)-/
theorem algebra_167956 (f : ℝ → ℝ) (h : ∀ x y, f x * f y = f (x - y)) :
    f 2017 = 0 ∨ f 2017 = 1 := by

-- we first show that f(0) is either 0 or 1, because fx ^2 = f(0) for all x
  have h0 : f 0 * f 0 = f 0 := by 
    specialize h 0 0
    norm_num at h
    linarith
  have hfx_sq : ∀ x, f x ^ 2 = f 0 := by  -- key step 
    intro x
    have h1 := h x x
    simp at h1
    linarith
  have h0_eq : f 0 = 0 ∨ f 0 = 1 := by
    have h1 : f 0 * (f 0 - 1) = 0 := by linarith [h0]
    cases (mul_eq_zero.mp h1) with
    | inl h0 => left; linarith
    | inr h0 => right; linarith
  cases h0_eq with
  | inl h0_eq_0 =>
    have h_all_zero : ∀ x, f x = 0 := by  -- in this case, we show that f(x) = 0 for all x
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
    have h1 : f 2017 = 1 ∨ f 2017 = -1 := by
      rw [sq_eq_one_iff] at h2017_sq
      exact h2017_sq 
    cases h1 with
    | inl h2017_eq_1 =>
      right
      exact h2017_eq_1
    | inr h2017_eq_neg1 =>  --- in this case, we show the contradiction
      have h2017_div_2 : f (2017 / 2) = 0 := by
        have h_eq1 := h 2017 (2017 / 2)
        rw [h2017_eq_neg1] at h_eq1
        norm_num at h_eq1
        nlinarith  
      specialize hfx_sq (2017 / 2)
      rw [h2017_div_2] at hfx_sq
      rw [h0_eq_1] at hfx_sq
      simp at hfx_sq
      