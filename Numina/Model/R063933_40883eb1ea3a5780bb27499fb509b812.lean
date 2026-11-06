import Mathlib

theorem number_theory_1193 (n : ℤ) : ∃ k, n ^ 4 = 5 * k ∨ n ^ 4 = 5 * k + 1 := by 
  have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
    omega
  
  rcases h1 with (h | h | h | h | h)
  
  · -- Case n % 5 = 0
    use (n ^ 4) / 5
    left
    have h2 : n ^ 4 % 5 = 0 := by 
      have h3 : n % 5 = 0 := h
      have h4 : n ^ 4 % 5 = 0 := by 
        simp [pow_succ, Int.mul_emod, h3]
      exact h4
    omega
  
  · -- Case n % 5 = 1
    use (n ^ 4 - 1) / 5
    right
    have h2 : n ^ 4 % 5 = 1 := by
      have h3 : n % 5 = 1 := h
      have h4 : n ^ 4 % 5 = 1 := by 
        simp [pow_succ, Int.mul_emod, h3]
      exact h4
    omega
  
  · -- Case n % 5 = 2
    use (n ^ 4 - 1) / 5
    right
    have h2 : n ^ 4 % 5 = 1 := by 
      have h3 : n % 5 = 2 := h
      have h4 : n ^ 4 % 5 = 1 := by 
        simp [pow_succ, Int.mul_emod, h3]
      exact h4
    omega

  · -- Case n % 5 = 3
    use (n ^ 4 - 1) / 5
    right
    have h2 : n ^ 4 % 5 = 1 := by 
      have h3 : n % 5 = 3 := h
      have h4 : n ^ 4 % 5 = 1 := by 
        simp [pow_succ, Int.mul_emod, h3]
      exact h4
    omega
  
  · -- Case n % 5 = 4
    use (n ^ 4 - 1) / 5
    right
    have h2 : n ^ 4 % 5 = 1 := by 
      have h3 : n % 5 = 4 := h
      have h4 : n ^ 4 % 5 = 1 := by 
        simp [pow_succ, Int.mul_emod, h3]
      exact h4
    omega