import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_284676 (n : ℕ) (hn : n > 0) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + b = 2) :
  1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by

  have h1 : b = 2 - a := by linarith

  have h2 : a < 2 := by linarith
  have h3 : a * b ≤ 1 := by
    rw [h1]
    have h4 : a * (2 - a) ≤ 1 := by
      have h5 : a * (2 - a) = - (a - 1) ^ 2 + 1 := by
        nlinarith
      rw [h5]
      have h6 : - (a - 1) ^ 2 ≤ 0 := by
        have h7 : (a - 1) ^ 2 ≥ 0 := sq_nonneg (a - 1)
        linarith
      linarith
    linarith

  have h4 : (a * b) ^ n ≤ 1 := by
    have h5 : a * b ≤ 1 := h3
    have h6 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals
        nlinarith [show 0 < a * b from mul_pos ha hb]
    have h7 : (1 : ℝ) ^ n = 1 := by
      have h8 : ∀ n : ℕ, (1 : ℝ) ^ n = 1 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => 
          simp [pow_succ] at ih ⊢
      specialize h8 n
      linarith
    linarith [h7]

  have h5 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 ≥ 0 := by
    have h7 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1) =
        ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) / ((1 + a ^ n) * (1 + b ^ n)) := by 
      field_simp
      <;> ring
    rw [h7] at *
    apply div_nonneg
    have h8 : (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) = 1 - (a ^ n * b ^ n) := by
      ring_nf
    rw [h8]
    have h10 : a ^ n * b ^ n ≤ (1 : ℝ) := by
      have h11 : a * b ≤ (1 : ℝ) := h3
      have h12 : a ^ n * b ^ n = (a * b) ^ n := by 
        rw [mul_pow]
      rw [h12]
      linarith [h4]
    linarith
    positivity

  linarith [h5]