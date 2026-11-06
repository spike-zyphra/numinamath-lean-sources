import Mathlib

theorem algebra_96923 {a b : ℕ → ℕ} {α β : ℕ} (ha : ∀ n, a n = 1 + α * n)
    (hb : ∀ n, b n = β ^ n) (c : ℕ → ℕ) (hc : ∀ n, c n = a n + b n) :
    ∃ k, c (k - 1) = 100 ∧ c (k + 1) = 1000 → c k = 262 := by
  use 0
  intro h
  simp [hc, ha, hb] at h ⊢
  all_goals omega