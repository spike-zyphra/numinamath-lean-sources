import Mathlib

theorem number_theory_23146 :
  IsGreatest {x | ∃ n:ℕ , n > 0 ∧ x = Nat.gcd (n + 7) (2 * n + 1)} 13 := by 
  constructor
  · -- Show that 13 is in the set
    use 6
    all_goals norm_num
  · -- Show that 13 is greatest in the set
    intro x hx
    rcases hx with ⟨n, hn_pos, hx⟩
    rw [hx]
    have h1 : Nat.gcd (n + 7) (2 * n + 1) ∣ (n + 7) := by 
      apply Nat.gcd_dvd_left
    have h2 : Nat.gcd (n + 7) (2 * n + 1) ∣ (2 * n + 1) := by
      apply Nat.gcd_dvd_right
    -- Now to show that Nat.gcd (n + 7) (2 * n + 1) divides 13, which will show that it is at most 13.
    have h3 : Nat.gcd (n + 7) (2 * n + 1) ∣ 13 := by
      have h5 : Nat.gcd (n + 7) (2 * n + 1) ∣ (2 * (n + 7)) := by 
        apply Nat.dvd_trans h1
        simp
      have h6 : Nat.gcd (n + 7) (2 * n + 1) ∣ (2 * n + 1 : ℕ) := h2
      -- Now that we can form the linear combination 2 * (n + 7) - (2 * n + 1) which is equal to 13
      have h7 : Nat.gcd (n + 7) (2 * n + 1) ∣ ((2 * (n + 7) : ℕ) - (2 * n + 1 : ℕ)) := by 
        apply Nat.dvd_sub' 
        · exact h5
        · exact h2
      -- Compute that the result is 13
      have h8 : (2 * (n + 7) : ℕ) - (2 * n + 1 : ℕ) = 13 := by 
        omega
      -- Now rewrite h7 with h8
      rw [h8] at h7 
      exact h7 
    -- Now we get that Nat.gcd (n + 7) (2 * n + 1) ≤ 13 since it divides 13 which is prime.
    have h4 : Nat.gcd (n + 7) (2 * n + 1) ≤ 13 := by 
      exact Nat.le_of_dvd (by norm_num) h3
    linarith