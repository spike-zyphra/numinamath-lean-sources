import Mathlib

theorem algebra_252906 (x : ℕ) (h : 27^x + 12^x = 2 * 8^x) : x = 0 := by
  by_cases h2 : x > 0
  · -- Assume x > 0, need to derive a contradiction
    have eq1 : 27^x + 12^x > 2 * 8^x := by
      have h3 : ∀ x : ℕ, x > 0 → 27^x + 12^x > 2 * 8^x := by
        intro x hx
        have base1 : 27 ^ 1 + 12 ^ 1 > 2 * 8 ^ 1 := by norm_num
        have step1 : ∀ (k : ℕ), k > 0 → 27 ^ k + 12 ^ k > 2 * 8 ^ k →
          27 ^ (k + 1) + 12 ^ (k + 1) > 2 * 8 ^ (k + 1) := by
          intro k hk h1
          simp [pow_succ, pow_mul] at h1 ⊢
          nlinarith [show (27 : ℕ) ^ k > 0 by positivity,
            show (12 : ℕ) ^ k > 0 by positivity,
            show (8 : ℕ) ^ k > 0 by positivity,
            show (27 : ℕ) ^ 1 > 0 by norm_num,
            show (12 : ℕ) ^ 1 > 0 by norm_num,
            show (8 : ℕ) ^ 1 > 0 by norm_num
          ]
        exact Nat.le_induction base1 step1 x hx
      apply h3 x h2
    linarith
  · -- x ≤ 0
    have h3 : x = 0 := by linarith
    exact h3