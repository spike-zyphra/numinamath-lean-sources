import Mathlib

theorem number_theory_174672 (n : ℕ) (h₀ : ¬ 3 ∣ n) (h₁ : ¬ 3 ∣ n + 1) :
    (n * (n + 1)) % 9 = 2 := by
  have h3 : n % 3 = 1 := by
    have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h5 with (h | h | h)
    · -- n % 3 = 0
      have h6 : 3 ∣ n := by
        omega
      contradiction
    · -- n % 3 = 1
      tauto
    · -- n % 3 = 2
      have h8 : (n + 1) % 3 = 0 := by
        omega
      have h9 : 3 ∣ n + 1 := by 
        omega
      contradiction
  have h4 : n % 9 = 1 ∨ n % 9 = 4 ∨ n % 9 = 7 := by
    omega
  rcases h4 with (h | h | h)
  · -- n % 9 = 1
    simp [Nat.mul_mod, Nat.add_mod, h] at *
    all_goals omega
  · -- n % 9 = 4
    simp [Nat.mul_mod, Nat.add_mod, h] at *
    all_goals omega
  · -- n % 9 = 7
    simp [Nat.mul_mod, Nat.add_mod, h] at *
    all_goals omega