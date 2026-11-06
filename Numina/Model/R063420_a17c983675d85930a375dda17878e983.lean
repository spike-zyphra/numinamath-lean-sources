import Mathlib

theorem algebra_307154 {a b c : ℝ} (h₀ : a + b = 8) (h₁ : a * b - c ^ 2 + 8 * Real.sqrt 2 * c = 48) :
    ∃ x₁ x₂, x₁ ^ 2 * b + c * x₁ - a = 0 ∧ x₂ ^ 2 * b + c * x₂ - a = 0 ∧
    x₁ = (-Real.sqrt 2 + Real.sqrt 6) / 2 ∧ x₂ = (-Real.sqrt 2 - Real.sqrt 6) / 2 := by
  have h2 : b = 8 - a := by linarith
  rw [h2] at h₁
  have h3 : (a - 4) ^ 2 + (c - 4 * Real.sqrt 2) ^ 2 = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have ha : a = 4 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * Real.sqrt 2)]
  have hc : c = 4 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * Real.sqrt 2)]
  have hb : b = 4 := by
    linarith [h₀, ha]
  use (-Real.sqrt 2 + Real.sqrt 6) / 2, (-Real.sqrt 2 - Real.sqrt 6) / 2
  constructor
  · -- Show that x₁ is a root of the quadratic equation
    rw [hb, hc, ha]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (0 : ℝ) ≤ (6 : ℝ)),
      mul_self_nonneg (Real.sqrt 2 - Real.sqrt 6)]
  constructor
  · -- Show that x₂ is a root of the quadratic equation
    rw [hb, hc, ha]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (0 : ℝ) ≤ (6 : ℝ)),
      mul_self_nonneg (Real.sqrt 2 + Real.sqrt 6)]
  constructor
  · -- Show that x₁ equals (-√2 + √6)/2
    rfl
  · -- Show that x₂ equals (-√2 - √6)/2
    rfl