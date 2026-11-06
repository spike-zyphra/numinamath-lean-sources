import Mathlib

theorem number_theory_19592 :
    IsGreatest {x | ∃ n : ℕ, 0 < n ∧ x = Nat.gcd (13 * n + 8) (5 * n + 3)} 1 := by
  constructor
  · -- Show that 1 belongs to the set
    use 1
    all_goals norm_num
  · -- Show that 1 is the greatest element in the set
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    have h1 : Nat.gcd (13 * n + 8) (5 * n + 3) = 1 := by
      have h2 : Nat.gcd (13 * n + 8) (5 * n + 3) = Nat.gcd (5 * n + 3) (3 * n + 2) := by 
        rw [show 13 * n + 8 = 2 * (5 * n + 3) + (3 * n + 2) by omega]
        simp [Nat.gcd_comm]
      have h3 : Nat.gcd (5 * n + 3) (3 * n + 2) = Nat.gcd (3 * n + 2) (2 * n + 1) := by
        rw [show 5 * n + 3 = 1 * (3 * n + 2) + (2 * n + 1) by omega]
        simp [Nat.gcd_comm]
      have h4 : Nat.gcd (3 * n + 2) (2 * n + 1) = Nat.gcd (2 * n + 1) (n + 1) := by
        rw [show 3 * n + 2 = 1 * (2 * n + 1) + (n + 1) by omega]
        simp [Nat.gcd_comm]
      have h5 : Nat.gcd (2 * n + 1) (n + 1) = Nat.gcd (n + 1) n := by
        rw [show 2 * n + 1 = 1 * (n + 1) + n by omega]
        simp [Nat.gcd_comm]
      have h6 : Nat.gcd (n + 1) n = 1 := by
        have h7 : Nat.gcd (n + 1) n ∣ (n + 1) := by 
          apply Nat.gcd_dvd_left 
        have h8 : Nat.gcd (n + 1) n ∣ n := by 
          apply Nat.gcd_dvd_right 
        have h9 : Nat.gcd (n + 1) n ∣ 1 := by 
          have h10 : Nat.gcd (n + 1) n ∣ (n + 1) := h7
          have h11 : Nat.gcd (n + 1) n ∣ n := h8
          have h12 : Nat.gcd (n + 1) n ∣ ((n + 1) - n) := Nat.dvd_sub' h10 h11
          have h13 : (n + 1) - n = 1 := by omega 
          rw [h13] at h12 
          exact h12 
        have h10 : Nat.gcd (n + 1) n = 1 := by 
          exact Nat.dvd_one.mp h9 
        exact h10
      rw [h2, h3, h4, h5, h6]
    rw [hx]
    rw [h1]