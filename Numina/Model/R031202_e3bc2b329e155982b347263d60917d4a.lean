import Mathlib

theorem number_theory_115413 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = a * b * c) :
    a = 1 ∧ b = 2 ∧ c = 3 ∨ a = 1 ∧ b = 3 ∧ c = 2 ∨ a = 2 ∧ b = 1 ∧ c = 3 ∨
    a = 2 ∧ b = 3 ∧ c = 1 ∨ a = 3 ∧ b = 1 ∧ c = 2 ∨ a = 3 ∧ b = 2 ∧ c = 1 := by 
  have ha1 : a ≥ 1 := by 
    omega
  have hb1 : b ≥ 1 := by
    omega
  have hc1 : c ≥ 1 := by
    omega
  have h1 : a ≤ 3 := by
    by_contra h
    push_neg at h
    have h2 : b ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    have h3 : c ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    interval_cases b <;> interval_cases c <;> omega
  have h2 : b ≤ 3 := by
    by_contra h
    push_neg at h
    have h3 : a ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    have h4 : c ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    interval_cases a <;> interval_cases c <;> omega
  have h3 : c ≤ 3 := by
    by_contra h
    push_neg at h
    have h4 : a ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    have h5 : b ≤ 3 := by
      nlinarith [sq_nonneg ((a : ℕ) - 2 : ℤ), sq_nonneg ((b : ℕ) - 2 : ℤ), sq_nonneg ((c : ℕ) - 2 : ℤ), mul_pos (show 0 < a by omega) (show 0 < b by omega), mul_pos (show 0 < a by omega) (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
    interval_cases a <;> interval_cases b <;> omega
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega