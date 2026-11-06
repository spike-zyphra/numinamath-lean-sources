import Mathlib

open Real Set

theorem inequalities_130104 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧ x = (3 * a ^ 2 - a) / (1 + a ^ 2) +
      (3 * b ^ 2 - b) / (1 + b ^ 2) + (3 * c ^ 2 - c) / (1 + c ^ 2)} 0 := by 
  constructor 
  · -- Show 0 is in the set
    use 1 / 3, 1 / 3, 1 / 3 
    norm_num 
  · -- Show no negative is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq1, heq⟩ 
    have h1 : (3 * a ^ 2 - a) / (1 + a ^ 2) + (3 * b ^ 2 - b) / (1 + b ^ 2) + (3 * c ^ 2 - c) / (1 + c ^ 2) ≥ 0 := by
      have h2a : (3 * a ^ 2 - a) / (1 + a ^ 2) ≥ (9 / 10) * (a - 1 / 3) := by
        apply (le_div_iff₀ (by positivity : 1 + a ^ 2 > 0)).mpr 
        nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3 - 3 / 5), sq_nonneg (a ^ 2 - 1 / 3), sq_nonneg (a * (a - 1 / 3)), mul_pos ha (show 0 < 1 + a ^ 2 by positivity)]
      have h2b : (3 * b ^ 2 - b) / (1 + b ^ 2) ≥ (9 / 10) * (b - 1 / 3) := by 
        apply (le_div_iff₀ (by positivity : 1 + b ^ 2 > 0)).mpr 
        nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b + 1 / 3 - 3 / 5), sq_nonneg (b ^ 2 - 1 / 3), sq_nonneg (b * (b - 1 / 3)), mul_pos hb (show 0 < 1 + b ^ 2 by positivity)]
      have h2c : (3 * c ^ 2 - c) / (1 + c ^ 2) ≥ (9 / 10) * (c - 1 / 3) := by 
        apply (le_div_iff₀ (by positivity : 1 + c ^ 2 > 0)).mpr 
        nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c + 1 / 3 - 3 / 5), sq_nonneg (c ^ 2 - 1 / 3), sq_nonneg (c * (c - 1 / 3)), mul_pos hc (show 0 < 1 + c ^ 2 by positivity)]
      linarith [h2a, h2b, h2c, h_eq1]
    linarith [heq, h1]