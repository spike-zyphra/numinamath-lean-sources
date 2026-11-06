import Mathlib

open Real

theorem inequalities_116106 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a + b) / (a + c) = 1 / (1 + c / a) + 1 / (a / b + c / b)) :
    (a / b + c / a + b / c) ≤ (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) := by
  -- We need to prove (a / b + c / a + b / c) ≤ (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2)
  -- Multiplying both sides by a^2 * b^2 * c^2 to clear denominators
  -- Left side multiplied: (a / b + c / a + b / c) * a^2 * b^2 * c^2 = a^3 * b * c^2 + a * b^2 * c^3 + a^2 * b^3 * c
  -- Right side multiplied: (b^2 / a^2 + c^2 / b^2 + a^2 / c^2) * a^2 * b^2 * c^2 = b^4 * c^2 + a^2 * c^4 + a^4 * b^2
  -- Therefore, the inequality reduces to proving:
  -- a^3 * b * c^2 + a * b^2 * c^3 + a^2 * b^3 * c ≤ b^4 * c^2 + a^2 * c^4 + a^4 * b^2
  -- Let's prove this polynomial inequality in Lean.
  have h1 : (a / b + c / a + b / c) ≤ (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) := by
    have pos1 : a ^ 2 * b ^ 2 * c ^ 2 > 0 := by positivity
    have h2 : (a / b + c / a + b / c) * (a ^ 2 * b ^ 2 * c ^ 2) ≤ (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) * (a ^ 2 * b ^ 2 * c ^ 2) := by
      have h3 : (a / b + c / a + b / c) * (a ^ 2 * b ^ 2 * c ^ 2) = (a ^ 3 * b * c ^ 2 + a * b ^ 2 * c ^ 3 + a ^ 2 * b ^ 3 * c) := by
        field_simp [ha, hb, hc]
        ring
      have h4 : (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) * (a ^ 2 * b ^ 2 * c ^ 2) = (b ^ 4 * c ^ 2 + a ^ 2 * c ^ 4 + a ^ 4 * b ^ 2) := by
        field_simp [ha, hb, hc]
        ring
      rw [h3, h4]
      nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a * c - b * c), sq_nonneg (a * b - c * a), sq_nonneg (a * b - c * b),
        mul_ne_zero_iff.1 (show a * b ≠ 0 by simp [ha, hb]), mul_ne_zero_iff.1 (show b * c ≠ 0 by simp [hb, hc]), mul_ne_zero_iff.1 (show a * c ≠ 0 by simp [ha, hc]),
        sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    have pos2 : (a ^ 2 * b ^ 2 * c ^ 2 : ℝ) > 0 := pos1
    have h5 : (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) = ( (b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2) * (a ^ 2 * b ^ 2 * c ^ 2) ) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp [ha, hb, hc]
      <;> ring
    have h6 : (a / b + c / a + b / c) = ( (a / b + c / a + b / c) * (a ^ 2 * b ^ 2 * c ^ 2) ) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp [ha, hb, hc]
      <;> ring
    rw [h6, h5]
    apply (div_le_div_right pos2).mpr
    linarith [h2]
  linarith [h1]