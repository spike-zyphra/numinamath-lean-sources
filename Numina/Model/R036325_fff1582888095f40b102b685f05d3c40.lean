import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_60505 (a b c : ℝ) 
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a < b) 
    (h1 : a * a ^ 2 - b * a + c = 0) (h2 : a * b ^ 2 - b * b + c = 0) 
    (ht : a + c > b ∧ a + b > c ∧ b + c > a):
    7 / 8 < a + b - c ∧ a + b - c < Real.sqrt 5 - 1 := by 
  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have htc1 : a + c > b := ht.1
  have htc2 : a + b > c := ht.2.1
  have htc3 : b + c > a := ht.2.2
  have hc1 : c = a * b - a ^ 3 := by
    nlinarith [h1]
  have hc2 : c = b ^ 2 - a * b ^ 2 := by
    nlinarith [h2]
  have heq2 : a * b - a ^ 3 = b ^ 2 - a * b ^ 2 := by
    linarith [hc1, hc2]
  have heq3 : (a - b) * (a ^ 2 + a * b - b) = 0 := by
    nlinarith [heq2]
  cases (mul_eq_zero.mp heq3) with
  | inl hbl =>
    nlinarith
  | inr heq4 =>
    have heq5 : 0 < 1 - a := by 
      nlinarith [hb1, heq4]
    have hb_eq : b = a^2 / (1 - a) := by 
      field_simp [ne_of_gt heq5]
      nlinarith
    have hc_eq : c = a^4 / (1 - a) := by 
      have hb_eq' : b = a^2 / (1 - a) := hb_eq
      have hc_eq1 : c = a * b - a ^ 3 := by 
        nlinarith [h1]
      rw [hc_eq1, hb_eq']
      field_simp [ne_of_gt heq5]
      <;> nlinarith
    have h3 : a + b - c = a^3 + a^2 + a := by 
      have hb_eq' : b = a^2 / (1 - a) := hb_eq
      have hc_eq' : c = a^4 / (1 - a) := hc_eq
      field_simp [ne_of_gt (show 0 < 1 - a by nlinarith [hb_eq, hb1]) ] at hb_eq' hc_eq' ⊢
      nlinarith
    have h4 : 0 < 1 - a := by nlinarith [hb1, heq4]
    have h5 : a < 1 := by nlinarith
    have h6 : a + b - c = a^3 + a^2 + a := h3
    have h7 : 7 / 8 < a + b - c := by 
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - (Real.sqrt 5 - 1) / 2), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    have h8 : a + b - c < Real.sqrt 5 - 1 := by 
      nlinarith [sq_nonneg (a - (Real.sqrt 5 - 1) / 2), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    constructor
    · nlinarith [h7, h6]
    · nlinarith [h8, h6]