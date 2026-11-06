import Mathlib

theorem number_theory_272362 {a : ℕ → ℕ} (ha0 : a 0 = 2) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = a n + a (n - 1)) (p k : ℕ) (hp : Nat.Prime p)
    (hpk : p ∣ a (2 * k) - 2) : p ∣ a (2 * k + 1) - 1 := by
  have h2 := han 0
  simp [ha0, ha1] at h2
  all_goals omega