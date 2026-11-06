import Mathlib

theorem algebra_305958 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x ∈ Set.Ioo (-1) 1, f x = x^2 - a * x + a / 2)
    (h₁ : ∀ x ∈ Set.Ioo (-1) 1, f x > 0) :
    0 < a ∧ a ≤ 2 := by
  have h2 : 0 < a := by
    have h3 : f 0 > 0 := by
      apply h₁ 0
      norm_num
    have h4 : f 0 = 0 ^ 2 - a * 0 + a / 2 := by
      apply h₀ 0
      norm_num
    rw [h4] at h3
    nlinarith
  have h3 : a ≤ 2 := by
    by_contra h
    push_neg at h
    have h4 : a > 2 := by nlinarith
    have h5 : ∃ x ∈ Set.Ioo (-1) 1, f x ≤ 0 := by
      have h100 : a ^ 2 - 2 * a > 0 := by nlinarith
      have h101 : Real.sqrt (a ^ 2 - 2 * a) > 0 := by positivity
      use (a - Real.sqrt (a ^ 2 - 2 * a)) / 2
      constructor
      · -- Show that (a - Real.sqrt (a^2 - 2*a)) / 2 ∈ (-1, 1)
        have h102 : -1 < (a - Real.sqrt (a ^ 2 - 2 * a)) / 2 := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 - 2 * a), Real.sq_sqrt (show a ^ 2 - 2 * a ≥ 0 by nlinarith)]
        have h103 : (a - Real.sqrt (a ^ 2 - 2 * a)) / 2 < 1 := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 - 2 * a), Real.sq_sqrt (show a ^ 2 - 2 * a ≥ 0 by nlinarith)]
        exact ⟨by linarith, by linarith⟩
      · -- Show that f ((a - Real.sqrt (a^2 - 2*a)) / 2) ≤ 0
        have h60 : f ((a - Real.sqrt (a ^ 2 - 2 * a)) / 2) ≤ 0 := by
          have h70 : f ((a - Real.sqrt (a ^ 2 - 2 * a)) / 2) = ((a - Real.sqrt (a ^ 2 - 2 * a)) / 2) ^ 2 - a * ((a - Real.sqrt (a ^ 2 - 2 * a)) / 2) + a / 2 := by
            apply h₀
            -- Show ((a - Real.sqrt (a ^ 2 - 2 * a)) / 2) ∈ (-1, 1)
            have h102 : -1 < (a - Real.sqrt (a ^ 2 - 2 * a)) / 2 := by
              nlinarith [Real.sqrt_nonneg (a ^ 2 - 2 * a), Real.sq_sqrt (show a ^ 2 - 2 * a ≥ 0 by nlinarith)]
            have h103 : (a - Real.sqrt (a ^ 2 - 2 * a)) / 2 < 1 := by
              nlinarith [Real.sqrt_nonneg (a ^ 2 - 2 * a), Real.sq_sqrt (show a ^ 2 - 2 * a ≥ 0 by nlinarith)]
            exact ⟨by linarith, by linarith⟩
          rw [h70]
          nlinarith [Real.sqrt_nonneg (a ^ 2 - 2 * a), Real.sq_sqrt (show a ^ 2 - 2 * a ≥ 0 by nlinarith)]
        linarith
    rcases h5 with ⟨x, hx, hx0⟩
    have h6 : f x > 0 := h₁ x hx
    linarith
  constructor
  · exact h2
  · exact h3