import Mathlib

open Real Set

theorem inequalities_195303 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b - 2)]
  have h4 : (a * b) ^ n ≤ 1 := by
    have h5 : 0 ≤ a * b := by positivity
    have h6 : a * b ≤ 1 := h3
    have h7 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals
        nlinarith
    have h8 : (1 : ℝ) ^ n = 1 := by
      simp
    nlinarith
  have h5 : 0 < (1 + a^n) * (1 + b^n) := by positivity
  have h6 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 ≥ 0 := by
    have h8 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1) =
        (1 - (a * b) ^ n) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      <;> ring_nf
      <;> simp [pow_succ]
      <;> ring
    rw [h8]
    apply div_nonneg
    · -- Show $1 - (a * b) ^ n \geq 0$
      nlinarith [show (a * b) ^ n ≤ 1 by linarith [h4]]
    · -- Show $0 \leq (1 + a^n)(1 + b^n)$
      positivity
  linarith