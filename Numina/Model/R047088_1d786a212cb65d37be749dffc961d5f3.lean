import Mathlib

open Real

/- Let $n$ be a natural number, $a$, $b$ be positive real numbers, and satisfy $a+b=2$, then the minimum value of $\frac{1}{1+{{a}^{n}}}+\frac{1}{1+{{b}^{n}}}$ is ___          ___. -/
theorem inequalities_9877 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by
  have h6 : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), h]
  have h7 : 0 < a * b := by
    apply mul_pos
    all_goals linarith
  have h8 : (a * b) ^ n ≤ 1 := by
    have h9 : a * b ≤ 1 := h6
    have h10 : a * b > 0 := h7
    have h11 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals nlinarith
    have h12 : (1 : ℝ) ^ n = 1 := by
      simp
    linarith
  have h9 : 0 < (1 + a ^ n : ℝ) := by
    positivity
  have h10 : 0 < (1 + b ^ n : ℝ) := by
    positivity
  have h11 : (1 + a ^ n : ℝ) * (1 + b ^ n) > 0 := by
    positivity
  have h12 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 ≥ 0 := by
    have h10 : (a ^ n) * (b ^ n) = (a * b) ^ n := by
      rw [mul_pow]
    have h11 : (a ^ n) * (b ^ n) ≤ 1 := by
      have h9 : (a * b) ^ n ≤ 1 := h8
      rw [mul_pow] at *
      nlinarith
    have h13 : 1 - (a ^ n) * (b ^ n) ≥ 0 := by
      linarith
    have h14 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1) = (1 - (a ^ n) * (b ^ n)) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      <;> ring_nf
    rw [h14]
    apply div_nonneg
    · linarith
    all_goals positivity
  linarith