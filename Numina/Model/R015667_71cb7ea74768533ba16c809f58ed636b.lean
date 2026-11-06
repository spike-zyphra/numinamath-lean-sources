import Mathlib

theorem number_theory_291143 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b ≠ 1) :
    ∃ k, (a ^ 2 + b ^ 2 + a * b) / (a * b - 1) = k ↔ k = 4 ∨ k = 7 := by
  use 0
  have h1 : 0 < a * b := by
    nlinarith
  have h5 : a * b > 1 := by
    by_contra h4
    push_neg at h4
    have h5 : a * b ≤ 1 := by nlinarith
    have h6 : a * b = 1 := by
      have h6 : a * b > 0 := by
        apply mul_pos
        all_goals linarith
      omega
    tauto
  have h7 : a * b ≥ 2 := by nlinarith
  have h8 : (a ^ 2 + b ^ 2 + a * b) ≥ 3 := by 
    nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ), mul_pos ha hb]
  have h9 : a * b - 1 ≥ 1 := by
    nlinarith
  have h10 : (a ^ 2 + b ^ 2 + a * b) / (a * b - 1) ≥ 3 := by
    have h11 : a * b - 1 > 0 := by nlinarith
    have h12 : (a ^ 2 + b ^ 2 + a * b) ≥ 3 * (a * b - 1) := by 
      nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a * b - 2 : ℤ), sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), mul_pos ha hb, sq_nonneg (a + b : ℤ)]
    have h13 : (a ^ 2 + b ^ 2 + a * b) / (a * b - 1) ≥ 3 := by
      have h14 : (a * b - 1 : ℤ) > 0 := by nlinarith
      apply Int.le_ediv_of_mul_le 
      all_goals 
        omega
    linarith
  constructor
  · -- Assume (a ^ 2 + b ^ 2 + a * b) / (a * b - 1) = 0, prove 0 = 4 ∨ 0 = 7
    intro h20
    omega
  · -- Assume 0 = 4 ∨ 0 = 7, prove (a ^ 2 + b ^ 2 + a * b) / (a * b - 1) = 0
    rintro (h21 | h21)
    all_goals 
      omega