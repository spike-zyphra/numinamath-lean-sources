import Mathlib

open Real
open scoped BigOperators

theorem inequalities_296851 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a^2 + b^2 = c^2) (n : ℕ) (hn : 2 ≤ n) :
  a^n + b^n ≤ c^n := by
  have ha1 : a ≤ c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), h]
  have hb1 : b ≤ c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), h]
  have h6 : (a / c) ^ 2 + (b / c) ^ 2 = 1 := by
    have h1 : a ^ 2 + b ^ 2 = c ^ 2 := h
    have hc_pos : c > 0 := hc
    have h2 : c ≠ 0 := by linarith
    field_simp at *
    <;> nlinarith [h1, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h]
  have h7 : (a / c) ^ n + (b / c) ^ n ≤ 1 := by
    have h8 : (a / c) ^ n ≤ (a / c) ^ 2 := by
      have h12 : 0 ≤ a / c := by positivity
      have h13 : a / c ≤ 1 := by
        have h14 : a ≤ c := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), h]
        have hc_pos : c > 0 := hc
        have h15 : a / c ≤ (c) / c := by
          apply (div_le_div_right hc_pos).mpr
          linarith [h14]
        have h16 : (c) / c = 1 := by
          field_simp [show c ≠ 0 by linarith]
        linarith [h15, h16]
      have h18 : (a / c) ^ n ≤ (a / c) ^ 2 := by
        have h19 : (a / c) ^ (n : ℕ) ≤ (a / c) ^ (2 : ℕ) := by
          apply pow_le_pow_of_le_one
          all_goals
            try linarith [h12, h13, show n ≥ 2 by linarith, show 2 ≤ n by linarith]
        linarith
      linarith
    have h9 : (b / c) ^ n ≤ (b / c) ^ 2 := by
      have h12 : 0 ≤ b / c := by positivity
      have h13 : b / c ≤ 1 := by
        have h14 : b ≤ c := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), h]
        have hc_pos : c > 0 := hc
        have h15 : b / c ≤ (c) / c := by
          apply (div_le_div_right hc_pos).mpr
          linarith [h14]
        have h16 : (c) / c = 1 := by
          field_simp [show c ≠ 0 by linarith]
        linarith [h15, h16]
      have h18 : (b / c) ^ n ≤ (b / c) ^ 2 := by
        have h19 : (b / c) ^ (n : ℕ) ≤ (b / c) ^ (2 : ℕ) := by
          apply pow_le_pow_of_le_one
          all_goals
            try linarith [h12, h13, show n ≥ 2 by linarith, show 2 ≤ n by linarith]
        linarith
      linarith
    have h13 : (a / c) ^ n + (b / c) ^ n ≤ (a / c) ^ 2 + (b / c) ^ 2 := by
      linarith [h8, h9]
    have h14 : (a / c) ^ 2 + (b / c) ^ 2 = 1 := h6
    linarith [h13, h14]
  -- Now convert back to the original variables
  have h12 : a ^ n + b ^ n ≤ c ^ n := by
    have h13 : (a ^ n + b ^ n) / (c ^ n) ≤ 1 := by
      have h14 : (a ^ n + b ^ n) / (c ^ n) = (a / c) ^ n + (b / c) ^ n := by
        field_simp [pow_add, pow_mul]
        <;> ring_nf <;> field_simp
        <;> ring
      rw [h14]
      linarith [h7]
    have hc_pos : c > 0 := hc
    have hn_pos : c ^ n > 0 := by positivity
    have h18 : a ^ n + b ^ n ≤ c ^ n := by
      have h19 : (a ^ n + b ^ n) / (c ^ n) ≤ 1 := h13
      have h20 : c ^ n > 0 := by positivity
      apply (div_le_iff₀ (by positivity)).mp at h19
      linarith
    linarith [h18, h13]
  exact h12