import Mathlib

theorem number_theory_23086 : IsGreatest { q : ℕ | ∀n, q ∣ ((2 * n + 1) + (2 * n + 3) + (2 * n + 5) + (2 * n + 7))} 8 := by 
  constructor 
  · -- Let's prove 8 is in the set.
    intro n 
    have h1 : (2 * n + 1 + (2 * n + 3) + (2 * n + 5) + (2 * n + 7)) = 8 * (n + 2) := by 
      omega 
    rw [h1] 
    simp [Nat.mul_comm] 
  · -- Now we prove no number greater than 8 is in the set.
    intro q hq 
    have h1 := hq 0 
    have h2 := hq 1 
    have h3 := hq 2 
    have h4 := hq 3 
    have h5 : q ∣ 16 := by 
      norm_num at h1 
      exact h1 
    have h6 : q ∣ 24 := by 
      norm_num at h2 
      exact h2 
    have h7 : q ∣ 8 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h5 h6) (by norm_num at h3; exact h3)) (by norm_num at h4; exact h4)
    have h8 : q ≤ 8 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    linarith