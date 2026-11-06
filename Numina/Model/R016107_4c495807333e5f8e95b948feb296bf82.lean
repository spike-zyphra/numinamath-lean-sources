import Mathlib

theorem number_theory_231990 (x y z : ℕ) (h : x + y + z = 1000)
    (h1 : x*1+y*2+z*5=2000) (h2 : Nat.Prime x) :
    x=3 ∧ y=996 ∧ z=1 := by
  have eq1 : y + 4 * z = 1000 := by
    omega
  have eq2 : x = 3 * z := by
    omega
  by_cases h3 : z > 1
  · -- Assume z > 1, then x >= 6 and divisible by 3
    have h4 : z ≥ 2 := by
      omega
    have h5 : x ≥ 6 := by
      omega
    have h6 : ¬ Nat.Prime x := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ x by
        omega
      ) (by
        omega
      ) (by
        omega
      )
    contradiction
  · -- Assume ¬(z > 1), so z ≤ 1
    have h4 : z ≤ 1 := by
      omega
    have h5 : z = 0 ∨ z = 1 := by
      omega
    rcases h5 with (h5 | h5)
    · -- Assume z = 0, then x = 0, not prime
      have h6 : z = 0 := by 
        omega
      have h7 : x = 0 := by
        omega
      rw [h7] at h2
      norm_num at h2
    · -- Assume z = 1, then x = 3, which is prime
      have h8 : z = 1 := by 
        omega
      have h9 : x = 3 := by 
        omega
      have h10 : y = 996 := by 
        omega
      constructor
      · exact h9
      constructor
      · exact h10
      · exact h8