import Mathlib

theorem number_theory_95911 (m n : ℕ) (hm : Odd m) (hn : Odd n) :
    Odd (3 * m * n) := by
  have h1 : m % 2 = 1 := by
    rcases hm with ⟨k, hk⟩
    omega
  have h2 : n % 2 = 1 := by
    rcases hn with ⟨j, hj⟩
    omega
  have h3 : (3 * m * n) % 2 = 1 := by
    simp [Nat.mul_mod, h1, h2]
  exact ⟨(3 * m * n) / 2, by omega⟩