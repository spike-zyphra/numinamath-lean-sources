import Mathlib

open Real Set
open scoped BigOperators

/- Find the minimum value of
\[\frac{\left( x + \dfrac{1}{x} \right)^6 - \left( x^6 + \dfrac{1}{x^6} \right) - 2}{\left( x + \dfrac{1}{x} \right)^3 + \left( x^3 + \dfrac{1}{x^3} \right)}\]for $x > 0.$ -/
theorem algebra_20754 :
  IsLeast {y : ℝ | ∃ x > 0, y = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3))} 6 := by
    -- 分两步证明：能取等 + 最小值
    constructor <;>
    simp [lowerBounds]
    -- 能取等
    .
      use 1
      simp
      norm_num
    -- 最小值
    .
      intro a x hx ha
      rw [show ((x + x⁻¹) ^ 6 - (x ^ 6 + (x ^ 6)⁻¹) - 2) = ((x + x⁻¹) ^ 6 - ((x ^ 6 + (x ^ 6)⁻¹) + 2)) by ring] at ha
      have h1 : (x ^ 6 + (x ^ 6)⁻¹ + 2) = (x ^ 3 + (x ^ 3)⁻¹) ^ 2:= by
        ring_nf
        field_simp
      rw [h1] at ha
      -- 简化表达式
      rw [show (x + x⁻¹) ^ 6 - (x ^ 3 + (x ^ 3)⁻¹) ^ 2 = ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) * ((x + x⁻¹) ^ 3 - (x ^ 3 + (x ^ 3)⁻¹)) by ring] at ha
      have h2 : (x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹) > 0:= by positivity
      rw [show ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) * ((x + x⁻¹) ^ 3 - (x ^ 3 + (x ^ 3)⁻¹)) / ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) = (((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) / ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹))) * ((x + x⁻¹) ^ 3 - (x ^ 3 + (x ^ 3)⁻¹)) by ring] at ha
      rw [show ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) / ((x + x⁻¹) ^ 3 + (x ^ 3 + (x ^ 3)⁻¹)) = 1 by field_simp] at ha
      have h3 : (x + x⁻¹) ^ 3 - (x ^ 3 + (x ^ 3)⁻¹) = 3 * (x + 1 / x):= by
        ring_nf
        field_simp
        ring_nf
      rw [h3] at ha
      simp at ha
      have h4 : x + x⁻¹ - 2 ≥ 0:= by
        field_simp
        rw [show x * x + 1 - x * 2 = (x - 1) ^ 2 by ring_nf]
        positivity
      linarith
