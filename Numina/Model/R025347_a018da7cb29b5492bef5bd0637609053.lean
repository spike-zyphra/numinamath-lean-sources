import Mathlib

theorem number_theory_257988 (n : ℕ) (hn : n > 0) :
    Nat.gcd (6 * n + 1) (15 * n + 2) = 1 := by 
  have h1 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ 1 := by
    have h4 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ (5 * (6 * n + 1) : ℕ) := by
      have h8 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ (6 * n + 1 : ℕ) := Nat.gcd_dvd_left (6 * n + 1) (15 * n + 2)
      have h9 : (6 * n + 1 : ℕ) ∣ 5 * (6 * n + 1 : ℕ) := by 
        use 5 
        all_goals ring 
      exact dvd_trans h8 h9 
    have h5 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ (2 * (15 * n + 2) : ℕ) := by 
      have h10 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ (15 * n + 2 : ℕ) := Nat.gcd_dvd_right (6 * n + 1) (15 * n + 2)
      have h11 : (15 * n + 2 : ℕ) ∣ 2 * (15 * n + 2 : ℕ) := by 
        use 2 
        all_goals ring 
      exact dvd_trans h10 h11 
    have h6 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ (5 * (6 * n + 1) - 2 * (15 * n + 2) : ℕ) := by 
      apply Nat.dvd_sub' 
      · exact h4 
      · exact h5 
    have h7 : (5 * (6 * n + 1) - 2 * (15 * n + 2) : ℕ) = 1 := by 
      omega 
    rw [h7] at h6 
    exact h6 
  have h8 : Nat.gcd (6 * n + 1) (15 * n + 2) = 1 := by 
    have h9 : Nat.gcd (6 * n + 1) (15 * n + 2) ∣ 1 := h1 
    have h10 : Nat.gcd (6 * n + 1) (15 * n + 2) = 1 := by 
      exact Nat.dvd_one.mp h9 
    exact h10 
  exact h8