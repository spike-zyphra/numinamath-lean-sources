import Mathlib

theorem algebra_94860 {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (h : ∀ n, a * r ^ n = a * r ^ (n + 1) + a * r ^ (n + 2)) :
    r = (Real.sqrt 5 - 1) / 2 := by
  have eq1 := h 0
  have eq2 : a = a * r + a * r ^ 2 := by
    simp [pow_zero, pow_one, pow_succ] at eq1
    linarith
  have h1 : r ^ 2 + r - 1 = 0 := by
    have h2 : a > 0 := ha
    have h3 : a * (1 : ℝ) = a * (r + r ^ 2) := by
      nlinarith [eq2]
    have h4 : (1 : ℝ) = r + r ^ 2 := by
      apply (mul_left_inj' (ne_of_gt ha)).mp 
      linarith
    nlinarith
  have h2 : r ^ 2 + r - 1 = 0 := h1
  have h3 : r = (Real.sqrt 5 - 1) / 2 := by
    have h4 : r ^ 2 + r - 1 = 0 := h1
    have h5 : r ^ 2 + r - 1 = (r - (Real.sqrt 5 - 1) / 2) * (r + (Real.sqrt 5 + 1) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h5] at h4
    cases (mul_eq_zero.mp h4) with
    | inl h6 =>
      linarith
    | inr h7 =>
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  exact h3