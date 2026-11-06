import Mathlib

theorem algebra_261610 (a : ℕ → ℝ) (ha : ∀ n, 0 < n → a n + a (n + 1) = 2 ^ n)
    (ha' : ∀ n, 0 < n → a n < a (n + 1)) :
    0 < a 1 ∧ a 1 < 1 := by

  have h1 := ha 1 (by norm_num)
  have h2 := ha 2 (by norm_num)
  have h3 := ha 3 (by norm_num)

  have h1' := ha' 1 (by norm_num)
  have h2' := ha' 2 (by norm_num)
  have h3' := ha' 3 (by norm_num)

  norm_num at h1 h2 h3 h1' h2' h3'

  constructor
  · -- We need to prove $0 < a_1$
    nlinarith
  · -- We need to prove $a_1 < 1$
    nlinarith