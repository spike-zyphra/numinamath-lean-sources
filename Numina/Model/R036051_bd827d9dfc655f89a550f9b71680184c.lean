import Mathlib

open Real

theorem inequalities_84363 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b^2 = 1 / 2) :
    4 ≤ 1 / (1 - a) + 1 / (1 - b) ∧
    (4 = 1 / (1 - a) + 1 / (1 - b) ↔ a = b) := by
  have h1 : a < 1 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h]
  have h2 : b < 1 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h]
  have h3 : 1 - a > 0 := by linarith
  have h4 : 1 - b > 0 := by linarith
  have h5 : 1 / (1 - a) + 1 / (1 - b) - 4 ≥ 0 := by
    have h8 : (1 - a) * (1 - b) > 0 := by positivity
    have h9 : 1 / (1 - a) + 1 / (1 - b) - 4 = ( -2 + 3 * a + 3 * b - 4 * a * b ) / ( (1 - a) * (1 - b) ) := by
      field_simp
      <;> ring
    rw [h9]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a * b - (1 / 4)), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), h, mul_pos ha (show 0 < (1 - a) by linarith), mul_pos hb (show 0 < (1 - b) by linarith), mul_pos ha hb ]
    positivity
  have h6 : 4 ≤ 1 / (1 - a) + 1 / (1 - b) := by linarith [h5]
  constructor 
  · linarith [h5]
  · -- Prove the equality holds iff a = b
    constructor
    · -- (→): if 4 = 1 / (1 - a) + 1 / (1 - b) then a = b
      intro h_eq
      have h8 : 1 / (1 - a) + 1 / (1 - b) -4 = 0 := by linarith [h_eq, h5]
      have h9 : (1 - a) * (1 - b) > 0 := by positivity
      have h10 : -2 + 3 * a + 3 * b - 4 * a * b = 0 := by
        have h11 : 1 / (1 - a) + 1 / (1 - b) -4 = ( -2 + 3 * a + 3 * b - 4 * a * b ) / ( (1 - a) * (1 - b) ) := by
          field_simp
          <;> ring
        rw [h11] at h8
        field_simp [h9] at h8
        <;> linarith 
      have h7 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a * b - (1 / 4)), mul_pos ha (show 0 < (1 - a) by linarith), mul_pos hb (show 0 < (1 - b) by linarith), mul_pos ha hb ]
      have h8 : a - b = 0 := by 
        nlinarith 
      linarith 
    · -- (←): if a = b then 4 = 1 / (1 - a) + 1 / (1 - b)
      intro h_eq
      rw [show b = a by linarith [h_eq]]
      have h11 : a = 1 / 2 := by
        have h12 : a ^ 2 + a ^ 2 = 1 / 2 := by
          have h13 : b = a := by linarith [h_eq]
          rw [show b = a by linarith [h_eq]] at h
          linarith 
        nlinarith 
      rw [h11]
      norm_num