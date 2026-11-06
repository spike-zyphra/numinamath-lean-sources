import Mathlib

open Real
open scoped BigOperators
/-let a,b,c be the side lengths of a triangle. Prove that
(a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c +
  (c ^ 2 + a ^ 2) * (c + b) / a ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2)-/
theorem inequalities_79152 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  (a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c +
  (c ^ 2 + a ^ 2) * (c + b) / a ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  
  -- prove a^2+b^2≥2ab 
    have h1 : (a ^ 2 + b ^ 2) * (a + c) / b ≥ 2 * a * (a + c) := by
      have h1 : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
        nlinarith [sq_nonneg (a - b)]
      have h2 : (a ^ 2 + b ^ 2) * (a + c) ≥ 2 * a * b * (a + c) := by
        nlinarith [sq_nonneg (a - b), ha, hb, hc]
      have h3 : b > 0 := hb
      apply (le_div_iff₀ h3).mpr
      linarith
  -- similar for b c
    have h2 : (b ^ 2 + c ^ 2) * (b + a) / c ≥ 2 * b * (b + a) := by
      have h1 : b ^ 2 + c ^ 2 ≥ 2 * b * c := by
        nlinarith [sq_nonneg (b - c)]
      have h2 : (b ^ 2 + c ^ 2) * (b + a) ≥ 2 * b * c * (b + a) := by
        nlinarith [sq_nonneg (b - c), ha, hb, hc]
      have h3 : c > 0 := hc
      apply (le_div_iff₀ h3).mpr
      linarith
  -- c a
    have h3 : (c ^ 2 + a ^ 2) * (c + b) / a ≥ 2 * c * (c + b) := by
      have h1 : c ^ 2 + a ^ 2 ≥ 2 * c * a := by
        nlinarith [sq_nonneg (c - a)]
      have h2 : (c ^ 2 + a ^ 2) * (c + b) ≥ 2 * c * a * (c + b) := by
        nlinarith [sq_nonneg (c - a), ha, hb, hc]
      have h3 : a > 0 := ha
      apply (le_div_iff₀ h3).mpr
      linarith
  -- combine h1h2h3
    have h4 : (a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c + (c ^ 2 + a ^ 2) * (c + b) / a ≥
      2 * a * (a + c) + 2 * b * (b + a) + 2 * c * (c + b) := by
        linarith [h1, h2, h3]
  -- last step
    have h5 : 2 * a * (a + c) + 2 * b * (b + a) + 2 * c * (c + b) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]

    linarith [h4, h5]