import Mathlib

theorem number_theory_232350 : ¬∃ n m, n^2 - m^2 = 10 := by
  rintro ⟨n, m, h_eq⟩
  have h1 : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Nat.mul_mod, h2]
    all_goals omega
  have h2 : m^2 % 4 = 0 ∨ m^2 % 4 = 1 := by
    have h3 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases h3 with (h3 | h3 | h3 | h3) <;> simp [pow_two, Nat.mul_mod, h3]
    all_goals omega
  have h3 : n^2 = m^2 + 10 := by
    omega
  have h4 : n^2 % 4 = (m^2 + 10) % 4 := by
    omega
  have h5 : (m^2 + 10) % 4 = (m^2 % 4 + 2) % 4 := by
    omega
  rw [h5] at h4
  omega