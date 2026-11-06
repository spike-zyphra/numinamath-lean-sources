import Mathlib

theorem algebra_10798 (N B J : ℕ) (hN : N > 1) (hB : B > 0) (hJ : J > 0)
    (h : N * B * 4 + N * J * 5 = 253) :
    (N * J * 5) / 100 = (1.65 : ℚ) := by

  have eq1 : N ≤ 253 := by
    nlinarith
  
  have h1 : N ∣ 253 := by
    use (B * 4 + J * 5)
    linarith [h]

  have h2 : N = 11 ∨ N = 23 ∨ N = 253 := by
    have h3 : N ∣ 253 := h1
    have : N ≤ 253 := by
      exact Nat.le_of_dvd (by norm_num) h3
    interval_cases N <;> tauto
  
  rcases h2 with hN11 | hN23 | hN253

  · -- N = 11
    have hN11' : N = 11 := hN11
    have eq2 : B = 2 := by
      simp [hN11'] at h 
      omega
    have eq3 : J = 3 := by
      simp [hN11', eq2] at h 
      omega
    have eq4 : N * J * 5 = 165 := by 
      simp [hN11', eq3]
    have eq5 : (N * J * 5 : ℚ) / 100 = (1.65 : ℚ) := by
      have eq6 : (N * J * 5 : ℚ) = (165 : ℚ) := by
        exact_mod_cast eq4
      rw [eq6]
      norm_num
    exact_mod_cast eq5

  · -- N = 23
    have hN23' : N = 23 := hN23 
    simp [hN23'] at h 
    all_goals
      exfalso
      omega

  · -- N = 253
    have hN253' : N = 253 := hN253
    simp [hN253'] at h 
    all_goals
      exfalso 
      omega