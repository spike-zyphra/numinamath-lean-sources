import Mathlib

theorem number_theory_315037 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h : ∀ n ≥ 2, a (n + 1) = sInf {p | p.Prime ∧ p ∣ a (n - 1) + a n}) :
    ∃ q : ℚ, q = ∑' n, a n / 10 ^ n := by
  let q := ∑' n, (a n) / 10 ^ n
  use q
  all_goals
  simp