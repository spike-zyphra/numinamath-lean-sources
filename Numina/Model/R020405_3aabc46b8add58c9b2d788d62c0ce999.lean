import Mathlib

theorem number_theory_148346 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ Nat.gcd (2 * n - 3) (3 * n - 2) ≠ 1 := by
  intro N
  use 5 * (N + 1) + 4
  constructor
  · -- Show that n > N
    omega
  · -- Show that the gcd is not 1
    have h1 : Nat.gcd (2 * (5 * (N + 1) + 4) - 3) (3 * (5 * (N + 1) + 4) - 2) ≠ 1 := by
      have h2 : 2 * (5 * (N + 1) + 4) - 3 = 5 * (2 * N + 3) := by 
        omega 
      have h3 : 3 * (5 * (N + 1) + 4) - 2 = 5 * (3 * N + 5) := by 
        omega 
      rw [h2, h3]
      have h4 : Nat.gcd (5 * (2 * N + 3)) (5 * (3 * N + 5)) ≥ 5 := by 
        have h8 : 5 ∣ Nat.gcd (5 * (2 * N + 3)) (5 * (3 * N + 5)) := by 
          have h10 : 5 ∣ 5 * (2 * N + 3) := by 
            omega 
          have h11 : 5 ∣ 5 * (3 * N + 5) := by 
            omega 
          exact Nat.dvd_gcd h10 h11 
        have h7 : Nat.gcd (5 * (2 * N + 3)) (5 * (3 * N + 5)) > 0 := by 
          have h9 : 5 * (2 * N + 3) > 0 := by 
            omega 
          have h10 : 5 * (3 * N + 5) > 0 := by 
            omega 
          have h11 : Nat.gcd (5 * (2 * N + 3)) (5 * (3 * N + 5)) > 0 := by 
            apply Nat.gcd_pos_of_pos_left 
            omega 
          linarith 
        omega 
      have h5 : Nat.gcd (5 * (2 * N + 3)) (5 * (3 * N + 5)) ≠ 1 := by 
        omega 
      exact h5 
    exact h1