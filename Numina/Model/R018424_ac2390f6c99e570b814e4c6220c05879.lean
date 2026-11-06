import Mathlib

theorem algebra_1182 {f : ℝ → ℝ} (h : ∀ x y, (f (x + y))^2 = f (x^2) + f (y^2)) : f 11 - f 0 = 0 := by
  have h1 : (f 0)^2 = 2 * f 0 := by
    specialize h 0 0
    norm_num at h
    linarith
  have h2 : ∀ x : ℝ, (f x)^2 = f (x^2) + f 0 := by
    intro x
    specialize h x 0
    norm_num at h
    linarith
  have h3 : (f 0)^2 = 2 * f 121 := by
    specialize h 11 (-11)
    norm_num at h
    linarith
  have h4 : (f 11)^2 = f 121 + f 0 := by
    specialize h 11 0
    norm_num at h
    linarith
  have h5 : (f 11) ^ 2 = (f 0) ^ 2 := by
    nlinarith [h3, h4]

  have h6 : (f 11) = f 0 ∨ (f 11) = - f 0 := by
    have h7 : (f 11) ^ 2 - (f 0) ^ 2 = 0 := by linarith
    have h8 : (f 11 - f 0) * (f 11 + f 0) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case f 11 - f 0 = 0
      left
      linarith
    · -- Case f 11 + f 0 = 0
      right
      linarith

  cases h6 with
  | inl h7 =>
    linarith
  | inr h7 =>
    have h8 : f 0 * (f 0 - 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h8) with
    | inl h9 =>
      have h10 : f 0 = 0 := by linarith
      have h11 : f 11 = 0 := by
        linarith [h7, h10]
      linarith
    | inr h10 =>
      have h11 : f 0 = 2 := by
        linarith
      have h12 : f 11 = -2 := by
        linarith [h7, h11]
      -- Now to find a contradiction
      -- Setting y = x, gives [f(2x)]^2 = 2f(x^2)
      -- Let x = sqrt(11), then [f(2*sqrt(11))]^2 = 2f(11) = 2*(-2) = -4
      -- Contradiction with a negative right side
      have h13 := h (Real.sqrt 11) (Real.sqrt 11)
      have h14 : (f (Real.sqrt 11 + Real.sqrt 11)) ^ 2 = -4 := by
        have h15 : (f (Real.sqrt 11 + Real.sqrt 11)) ^ 2 = f ((Real.sqrt 11) ^ 2) + f ((Real.sqrt 11) ^ 2) := by
          simpa using h13
        have h16 : f ((Real.sqrt 11) ^ 2) = f 11 := by
          rw [Real.sq_sqrt (by linarith)]
        rw [h15] 
        rw [h16]
        nlinarith
      have h15 : (f (Real.sqrt 11 + Real.sqrt 11)) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith