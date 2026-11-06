import Mathlib

theorem algebra_302528 {m n : ℕ} (h : (m * n + 9 * m + 11 * n + 145) % (m + 11) = 0)
    (h' : (m * n + 9 * m + 11 * n + 145) % (9 + n) = 0) (h'' : (m * n + 9 * m + 11 * n + 145) /
    (m + 11) = (m * n + 9 * m + 11 * n + 145) / (n + 9)) : (m * n + 9 * m + 11 * n + 145) / (m + 11)
    = 25 ∨ (m * n + 9 * m + 11 * n + 145) / (m + 11) = 47 := by
  rw [show m * n + 9 * m + 11 * n + 145 = (m + 11) * (n + 9) + 46 by ring] at h h'
  rw [Nat.mul_add_mod] at h; rw [show 9+n = n+9 by ring, Nat.mul_add_mod'] at h'
  rw [← Nat.dvd_iff_mod_eq_zero] at h h'
  replace h : m + 11 ∈ Nat.divisors 46 := by simp; exact h
  replace h' : n + 9 ∈ Nat.divisors 46 := by simp; exact h'
  have : Nat.divisors 46 = {1, 2, 23, 46} := by decide
  rw [this] at h h'; simp at h h'
  rcases h with h|h <;> rcases h' with h'|h'
  any_goals simp [h, h'] at h''
  all_goals simp [h, h']