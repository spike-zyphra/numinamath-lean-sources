import Mathlib

open Real

theorem inequalities_102404 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    69 / 4 ≤ (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ∧
    (69 / 4 = (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ↔
      (a = b ∧ b = c)) := by
  have h13 : (1 + a) > 0 := by nlinarith
  have h14 : (1 + b) > 0 := by nlinarith
  have h15 : (1 + c) > 0 := by nlinarith
  have h9 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) =
    ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b)) / ((1 + a) * (1 + b) * (1 + c)) := by
    field_simp
    ring
  have h9' : ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b)) / ((1 + a) * (1 + b) * (1 + c)) ≥ 69 / 4 := by
    have h91 : (7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b) ≥ 69 / 4 * ((1 + a) * (1 + b) * (1 + c)) := by
      have h6 : c = 1 - a - b := by
        nlinarith
      rw [show c = 1 - a - b by linarith [h6]]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), mul_pos ha hb, mul_pos ha (show (1 - a - b : ℝ) > 0 by nlinarith), mul_pos hb (show (1 - a - b : ℝ) > 0 by nlinarith)]
    have h7 : (1 + a) * (1 + b) * (1 + c) > 0 := by
      positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h91]
  have h23 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ≥ 69 / 4 := by
    linarith [h9, h9']
  constructor
  · -- Prove the inequality.
    linarith [h23]
  · -- Prove the equality condition.
    constructor
    · -- Assume equality holds, prove $a = b \land b = c$.
      intro heq
      have h25 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) = 69 / 4 := by
        linarith [heq]
      have h26 : ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b)) = (69 / 4) * ((1 + a) * (1 + b) * (1 + c)) := by
        field_simp [(show (1 + a : ℝ) ≠ 0 by positivity), (show (1 + b : ℝ) ≠ 0 by positivity), (show (1 + c : ℝ) ≠ 0 by positivity)] at h25 ⊢
        nlinarith [h25, h9]
      have eq61 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have eq62 : (a - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h28 : a - b = 0 := by
        rw [sq_eq_zero_iff] at eq61
        linarith
      have h29 : a - c = 0 := by
        rw [sq_eq_zero_iff] at eq62
        linarith
      constructor
      · -- $a = b$
        linarith [h28]
      · -- $b = c$
        nlinarith [h29, h28]
    · -- Assume $a = b \land b = c$, prove equality holds.
      rintro ⟨r1, r2⟩
      have ha1 : a = b := by linarith
      have ha2 : b = c := by linarith
      rw [show b = a by linarith [ha1], show c = a by nlinarith [ha2, ha1]]
      field_simp [(show (1 + a : ℝ) ≠ 0 by positivity), (show (1 + (a : ℝ) : ℝ) ≠ 0 by positivity), (show (1 + (a : ℝ) : ℝ) ≠ 0 by positivity)]
      nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a - 1 / 3), sq_nonneg (a - 1 / 3), mul_pos ha (show 0 < a by assumption), mul_pos ha (show 0 < a by assumption)]