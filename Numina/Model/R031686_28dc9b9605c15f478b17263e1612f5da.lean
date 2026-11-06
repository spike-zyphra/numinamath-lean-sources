import Mathlib

open Real

theorem inequalities_607925 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
(hord : a ≥ b ∧ b ≥ c) : (a^3 - c^3) / 3 ≥ a * b * c * ((a - b) / c + (b - c) / a)
∧ ((a^3 - c^3) / 3 = a * b * c * ((a - b) / c + (b - c) / a) ↔ a = c) := by
  have h1 : a ≥ b := hord.1
  have h2 : b ≥ c := hord.2
  constructor
  · -- Prove the inequality.
    have h3 : a ≥ c := by linarith
    have h4 : (a - b) ^ 3 + (b - c) ^ 3 ≥ 0 := by
      have h5 : (a - b) ≥ 0 := by linarith
      have h6 : (b - c) ≥ 0 := by linarith
      have h7 : (a - b) ^ 3 ≥ 0 := by
        apply pow_nonneg
        exact h5
      have h8 : (b - c) ^ 3 ≥ 0 := by
        apply pow_nonneg
        exact h6
      linarith
    have h8 : a ^ 3 - c ^ 3 ≥ 3 * (a * b * (a - b) + b * c * (b - c)) := by
      have h9 : (a - b) ^ 3 + (b - c) ^ 3 ≥ 0 := h4
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a - 2 * b + c), sq_nonneg (a - b + c)]
    have h9 : (a ^ 3 - c ^ 3) / 3 ≥ a * b * c * ((a - b) / c + (b - c) / a) := by
      have h10 : a * b * c * ((a - b) / c + (b - c) / a) = (a * b * (a - b) + b * c * (b - c)) := by
        field_simp [hc, ha]
        all_goals ring
      nlinarith
    linarith
  · -- When does equality hold?
    constructor
    · -- Prove the forward direction: If equality holds, then a = c.
      intro heq
      have h4 : (a - b) ^ 3 + (b - c) ^ 3 = 0 := by
        have h9 : a ^ 3 - c ^ 3 = 3 * (a * b * (a - b) + b * c * (b - c)) := by
          have h11 : (a ^ 3 - c ^ 3) / 3 = a * b * c * ((a - b) / c + (b - c) / a) := by linarith [heq]
          have h12 : a * b * c * ((a - b) / c + (b - c) / a) = (a * b * (a - b) + b * c * (b - c)) := by
            field_simp [hc, ha]
            all_goals ring
          have h14 : (a ^ 3 - c ^ 3) / 3 = (a * b * (a - b) + b * c * (b - c)) := by linarith [h11, h12]
          linarith
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a - 2 * b + c), sq_nonneg (a - b + c)]
      have h13 : (a - c) * ((a - b) ^ 2 - (a - b) * (b - c) + (b - c) ^ 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h13) with h16 h17
      · -- Case $a - c = 0$
        have ha2 : a = c := by linarith
        linarith
      · -- Case $(a - b)^2 - (a - b)(b - c) + (b - c)^2 = 0$
        have h18 : (a - b) ^ 2 - (a - b) * (b - c) + (b - c) ^ 2 = 0 := by linarith
        have h20 : (a - b) ^ 2 = 0 := by
          nlinarith [sq_nonneg (a - 2 * b + c), sq_nonneg (a - b - c), sq_nonneg (a - 2 * b + c), sq_nonneg (a - c)]
        have h21 : a - b = 0 := by
          nlinarith
        have h22 : (b - c) ^ 2 = 0 := by
          nlinarith [sq_nonneg (a - 2 * b + c), sq_nonneg (a - b - c), sq_nonneg (a - 2 * b + c), sq_nonneg (a - c)]
        have h23 : b - c = 0 := by
          nlinarith
        have ha2 : a = c := by
          nlinarith
        linarith
    · -- Backward direction: If a = c, then equality holds.
      intro heq
      have ha2 : a = c := by linarith
      rw [show c = a by linarith [ha2]]
      field_simp [ha]
      all_goals nlinarith