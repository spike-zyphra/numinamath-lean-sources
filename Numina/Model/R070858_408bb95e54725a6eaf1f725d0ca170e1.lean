import Mathlib

theorem number_theory_219094 (n : ℕ) (h : Odd n) : 3 ∣ n * (n + 2) * (n + 4) := by
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1 | h1)
  · -- Case where n % 3 = 0, so 3 divides n
    have : n * (n + 2) * (n + 4) % 3 = 0 := by
      simp [ Nat.mul_mod, Nat.add_mod, h1 ]
    exact Nat.dvd_of_mod_eq_zero this
  · -- Case where n % 3 = 1, so 3 divides n + 2
    have : n * (n + 2) * (n + 4) % 3 = 0 := by
      simp [ Nat.mul_mod, Nat.add_mod, h1 ]
      <;> omega
    exact Nat.dvd_of_mod_eq_zero this
  · -- Case where n % 3 = 2, so 3 divides n + 4
    have : n * (n + 2) * (n + 4) % 3 = 0 := by
      simp [ Nat.mul_mod, Nat.add_mod, h1 ]
      <;> omega
    exact Nat.dvd_of_mod_eq_zero this