import Mathlib

theorem algebra_272293 {a b c d : ℤ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) :
    ∃ p q : ℤ, (a + b * Real.sqrt 5) * (c + d * Real.sqrt 5) = p + q * Real.sqrt 5 ∧ p ≥ 0 ∧ q ≥ 0 := by
  use (a * c + 5 * b * d)
  use (a * d + b * c)
  constructor
  · -- Show that the product equals p + q * sqrt 5
    ring_nf
    <;> simp [Real.sqrt_mul_self, Real.sqrt_pos.mpr, show (5 : ℝ) ≥ 0 by norm_num]
    <;> ring_nf
    <;> norm_num
  constructor
  · -- Show p ≥ 0
    have hp1 : (a * c) ≥ 0 := mul_nonneg ha hc
    have hp2 : (5 * b * d) ≥ 0 := by
      have h1 : (5 : ℤ) * b ≥ 0 := mul_nonneg (show (5 : ℤ) ≥ 0 by norm_num) hb
      nlinarith
    linarith
  · -- Show q ≥ 0
    have hq1 : (a * d) ≥ 0 := mul_nonneg ha hd
    have hq2 : (b * c) ≥ 0 := mul_nonneg hb hc
    linarith