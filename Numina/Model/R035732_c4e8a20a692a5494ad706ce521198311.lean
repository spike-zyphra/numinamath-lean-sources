import Mathlib

open Real

theorem inequalities_234240 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (1 / 2) * (sqrt a + sqrt b + sqrt c) + (1 / (1 + a)) + (1 / (1 + b)) + (1 / (1 + c)) := by

  have h1 : ∀ x : ℝ, 0 < x → 1 ≤ (1 / 2) * sqrt x + (1 / (1 + x)) := by
    intro x hx
    have h2 : 0 < (1 + x) := by linarith
    have h3 : (1 / (1 + x)) = (1 + x)⁻¹ := by
      field_simp
    have h4 : (1 / 2) * sqrt x + (1 / (1 + x)) - 1 ≥ 0 := by
      have h5 : sqrt x ≥ 0 := by positivity
      have h6 : sqrt x * sqrt x = x := by
        rw [Real.mul_self_sqrt]
        linarith
      have h7 : 0 < (1 + x) := by linarith
      have h8 : (1 / 2) * sqrt x + (1 / (1 + x)) - 1 =
          ( sqrt x * (1 + x) + 2 - 2 * (1 + x) ) / (2 * (1 + x)) := by
        field_simp
      have h9 : (sqrt x * (1 + x) + 2 - 2 * (1 + x) ) / (2 * (1 + x)) ≥ 0 := by
        apply div_nonneg
        nlinarith [Real.sqrt_nonneg x, Real.mul_self_sqrt (show (0 : ℝ) ≤ x by nlinarith),
          sq_nonneg (sqrt x - 1), sq_nonneg (x - 1)]
        positivity
      linarith [h8, h9]
    linarith [h4]

  have h2 : 1 ≤ (1 / 2) * sqrt a + (1 / (1 + a)) := h1 a ha
  have h3 : 1 ≤ (1 / 2) * sqrt b + (1 / (1 + b)) := h1 b hb
  have h4 : 1 ≤ (1 / 2) * sqrt c + (1 / (1 + c)) := h1 c hc
  linarith [h2, h3, h4]