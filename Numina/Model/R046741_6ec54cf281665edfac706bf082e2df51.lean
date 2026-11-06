import Mathlib

theorem number_theory_7719 (n : ℕ) (hn : n > 0) (h1 : ∃ m, m^2 = 2 * n + 1) (h2 : ∃ p, p^2 = 3 * n + 1) :
    40 ∣ n := by
  rcases h1 with ⟨m, hm⟩
  rcases h2 with ⟨p, hp⟩
  have h3 : n % 5 = 0 := by
    by_contra h
    push_neg at h
    have h4 : m ^ 2 % 5 = 0 ∨ m ^ 2 % 5 = 1 ∨ m ^ 2 % 5 = 4 := by
      have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> norm_num [pow_two, Nat.mul_mod, h1] at *
    have h5 : p ^ 2 % 5 = 0 ∨ p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
      have h2 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Nat.mul_mod, h2] at *
    have eq1 : m ^ 2 % 5 = (2 * n + 1) % 5 := by
      omega
    have eq2 : p ^ 2 % 5 = (3 * n + 1) % 5 := by
      omega
    omega
  have h4 : n % 8 = 0 := by
    by_contra h
    push_neg at h
    have h5 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
      have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [pow_two, Nat.mul_mod, h1] at *
    have h6 : p ^ 2 % 8 = 0 ∨ p ^ 2 % 8 = 1 ∨ p ^ 2 % 8 = 4 := by
      have h2 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Nat.mul_mod, h2] at *
    have eq1 : m ^ 2 % 8 = (2 * n + 1) % 8 := by
      omega
    have eq2 : p ^ 2 % 8 = (3 * n + 1) % 8 := by
      omega
    omega
  omega