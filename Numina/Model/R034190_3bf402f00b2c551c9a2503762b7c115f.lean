import Mathlib
theorem number_theory_15831 : IsGreatest {x | ∀ n, (∃ k, 0 < k ∧ n = k + (k + 1) + (k + 2)) →  x ∣ n} 3 := by
  constructor
  · -- Show 3 is in the set.
    intro n hn
    rcases hn with ⟨k, hk, hn⟩
    have eq1 : n = 3 * (k + 1) := by 
      linarith
    rw [eq1]
    use k + 1
    all_goals ring
  · -- Show the greatest element is 3.
    intro x hx
    have h1 := hx 6 (by
      use 1 
      all_goals norm_num
    )
    
    have h2 := hx 9 (by 
      use 2 
      all_goals norm_num
    )
    
    have h4 : x ∣ 3 := by
      exact Nat.dvd_gcd h1 h2
    have h5 : x ≤ 3 := by 
      exact Nat.le_of_dvd (by norm_num) h4
    linarith