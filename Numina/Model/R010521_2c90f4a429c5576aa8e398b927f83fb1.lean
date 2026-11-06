import Mathlib

theorem algebra_169042 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 * b^2 * (a^2 * b^2 + 4) = 2 * (a^6 + b^6)) :
    Irrational a ∨ Irrational b := by
-- a^2 * b^2 * (a^2 * b^2 + 4) = 2 * (a^6 + b^6) is equivalent to
  -- (a ^ 4 - 2 * b ^ 2) * (b ^ 4 - 2 * a ^ 2) = 0.
  replace h : (a ^ 4 - 2 * b ^ 2) * (b ^ 4 - 2 * a ^ 2) = 0:= by linear_combination h
  -- We get a^4 - 2 * b^2 = 0 or b^4 - 2 * a^2 = 0.
  rw [mul_eq_zero] at h
  -- Without loss of generality, assume that a^4 - 2 * b^2 = 0.
  wlog h1 : a ^ 4 - 2 * b ^ 2 = 0
  · cases' h with h h
    · contradiction
    · rw [Or.comm]
      exact this hb ha (Or.inl h) h
  -- a^4 - 2 * b^2 = 0 implies that (a^2 / b)^2 = √2 ^ 2.
  replace h1 : (a ^ 2 / b) ^ 2 = √2 ^ 2 := by
    field_simp; linear_combination h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  -- It is enough to show that a^2 / b is irrational.
  suffices Irrational (a ^ 2 / b) by
    -- If a^2 / b is irrational then a^2 is irrational or b is irrational.
    have := this.div_cases
    cases' this with h h
    -- If a^2 is irrational then a is also irrational.
    · left
      apply Irrational.of_mul_self
      rw [← pow_two]
      exact h
    -- If b is irrational then we are done.
    · right
      exact h
  -- Now it is enough to show that either √2 or -√2 is irrational.
  cases' h1 with h1 h1
  · rw [h1]
    apply irrational_sqrt_two
  · rw [h1]
    have h4 : Irrational (-√2 : ℝ) := by
      apply Irrational.neg
      apply irrational_sqrt_two
    exact h4