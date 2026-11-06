import Mathlib

theorem algebra_297957 (a b m n : ℝ) (h₀ : a ≠ 0) (h₁ : m ≠ n)
    (h₂ : m^2 + a * m + b = 0) (h₃ : n^2 + a * n + b = 0)
    (h₄ : |m| + |n| ≤ 1) :
    |b| ≤ 1 / 2 ∧ b ≥ -1 / 2 := by
  have h5 : (m - n) * (m + n + a) = 0 := by
    nlinarith
  have h6 : m + n + a = 0 := by
    apply (mul_left_inj' (show m - n ≠ 0 by
      intro h
      apply h₁
      linarith)).mp
    linarith
  have h7 : a = - (m + n) := by
    linarith
  have h8 : b = m * n := by
    rw [show a = - (m + n) by linarith [h7] ] at h₂
    nlinarith
  have h9 : -1 / 2 ≤ b := by
    cases' abs_cases m with hm hm <;> cases' abs_cases n with hn hn
    all_goals
      nlinarith [sq_nonneg (m - n), sq_nonneg (m + n), sq_nonneg (m - n), sq_nonneg (m + n), sq_nonneg (m - n)]
  have h10 : b ≤ 1 / 2 := by
    cases' abs_cases m with hm hm <;> cases' abs_cases n with hn hn
    all_goals
      nlinarith [sq_nonneg (m - n), sq_nonneg (m + n), sq_nonneg (m - n), sq_nonneg (m + n), sq_nonneg (m - n)]
  have h11 : |b| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor
    · linarith [h9]
    · linarith [h10]
  constructor
  · linarith [h11]
  · linarith [h9]