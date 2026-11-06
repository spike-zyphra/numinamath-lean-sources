import Mathlib

theorem number_theory_116446 (n : ℕ) :
    ¬ Nat.Prime (6^n + 19) := by
  have h1 : ∀ k : ℕ, 6 ^ k % 5 = 1 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h2 : 6 ^ (k + 1) % 5 = (6 ^ k * 6) % 5 := by ring
      rw [h2]
      rw [Nat.mul_mod, ih]
      all_goals norm_num
      all_goals omega
  have h2 : (6 ^ n + 19) % 5 = 0 := by
    have h19 : 19 % 5 = 4 := by norm_num
    have h6n : 6 ^ n % 5 = 1 := h1 n
    calc
      (6 ^ n + 19) % 5 = (6 ^ n % 5 + 19 % 5) % 5 := by rw [Nat.add_mod]
      _ = (1 + 19 % 5) % 5 := by rw [h6n]
      _ = (1 + 4) % 5 := by rw [h19]
      _ = 0 := by norm_num
  have h3 : 5 ∣ 6 ^ n + 19 := by
    omega
  have h4 : 6 ^ n + 19 > 5 := by
    have h5 : ∀ k : ℕ, 6 ^ k ≥ 1 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        have h6 : 6 ^ (k + 1) = 6 ^ k * 6 := by ring
        rw [h6]
        nlinarith [ih]
    have h6n : 6 ^ n ≥ 1 := h5 n
    linarith
  have h5 : ¬ Nat.Prime (6 ^ n + 19) := by
    apply Nat.not_prime_of_dvd_of_lt h3 (by linarith) (by linarith)
  exact h5