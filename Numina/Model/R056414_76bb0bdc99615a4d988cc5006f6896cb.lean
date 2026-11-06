import Mathlib

theorem algebra_96470 (B J N : ℕ) (hB : B > 0) (hJ : J > 0) (hN : N > 1)
    (h : 4 * B * N + 5 * J * N = 253) :
    J * N * 5 = 165 := by
  
  have h1 : N ∣ 253 := by 
    use 4 * B + 5 * J
    linarith
  
  have h2 : N = 11 ∨ N = 23 ∨ N = 253 := by
    have h3 : N ≤ 253 := by 
      exact Nat.le_of_dvd (by norm_num) h1
    interval_cases N <;> omega
  
  rcases h2 with hN1 | hN2 | hN3
  
  · -- Case where N = 11.
    have h_eq1 : 4 * B + 5 * J = 23 := by
      rw [hN1] at h
      omega
    
    have hJ3 : J = 3 := by
      omega

    calc 
      J * N * 5 = 3 * 11 * 5 := by 
        rw [hJ3, hN1]
      _ = 165 := by norm_num
  
  · -- Case where N = 23. This will lead to a contradiction
    have h_eq2 : 4 * B + 5 * J = 11 := by
      rw [hN2] at h
      omega
    
    omega
  
  · -- Case where N = 253. This will lead to a contradiction
    have h_eq3 : 4 * B + 5 * J = 1 := by
      rw [hN3] at h
      omega

    omega