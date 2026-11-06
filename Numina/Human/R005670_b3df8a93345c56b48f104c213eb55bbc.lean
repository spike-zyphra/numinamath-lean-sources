import Mathlib

open Real

theorem my_favorite_theorem
    (p : ℕ → ℝ)
    (hp : ∀ n, p n = (Nat.factorial n) / (Nat.doubleFactorial (2 * n + 1))) :
    IsLeast {n : ℕ | 0 < n ∧ p n < 0.01} 6 := by
  constructor
  · constructor
    · norm_num
    · rw [hp 6]
      norm_num [Nat.factorial, Nat.doubleFactorial]
  · intro n hn
    rcases hn with ⟨hn_pos, hpn_lt⟩
    by_contra h
    push_neg at h
    have h1 : n < 6 := by linarith
    interval_cases n <;> simp [hp, Nat.factorial, Nat.doubleFactorial] at hpn_lt <;> norm_num at hpn_lt