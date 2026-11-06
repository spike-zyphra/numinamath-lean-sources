import Mathlib

open Real

theorem algebra_145357 {a : ℕ → ℝ}
    (ha : ∀ n, a n = ((5 + sqrt 13) / 2)^n - ((5 - sqrt 13) / 2)^n) :
    ∀ n ≥ 2, a n = 5 * a (n - 1) - 3 * a (n - 2) := by
  intro n hn
  have h1 : a n = ((5 + sqrt 13) / 2)^n - ((5 - sqrt 13) / 2)^n := ha n
  have h2 : a (n - 1) = ((5 + sqrt 13) / 2)^(n - 1) - ((5 - sqrt 13) / 2)^(n - 1) := ha (n - 1)
  have h3 : a (n - 2) = ((5 + sqrt 13) / 2)^(n - 2) - ((5 - sqrt 13) / 2)^(n - 2) := ha (n - 2)
  rw [h1, h2, h3]
  have h4 : ((5 + sqrt 13) / 2) ^ 2 = 5 * ((5 + sqrt 13) / 2) - 3 := by
    nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
  have h5 : ((5 - sqrt 13) / 2) ^ 2 = 5 * ((5 - sqrt 13) / 2) - 3 := by
    nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
  cases n with
  | zero =>
    linarith
  | succ n =>
    cases n with
    | zero =>
      linarith
    | succ n =>
      simp [pow_two, pow_succ, h4, h5]
      <;> ring_nf <;> simp [pow_two, pow_succ, h4, h5]
      <;> ring_nf