import Mathlib

theorem number_theory_232086 : {n : ℕ | n^2 ≡ 7 [MOD 10]}.encard = 0 := by
  have h1 : ∀ n : ℕ, ¬ (n^2 ≡ 7 [MOD 10]) := by
    intro n
    have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h | h) <;> norm_num [Nat.ModEq, Nat.pow_mod, h] at *
  have h2 : {n : ℕ | n^2 ≡ 7 [MOD 10]} = ∅ := by
    ext n
    simp [h1]
  rw [h2]
  simp