import Mathlib

theorem number_theory_149013 (a b c d m : ℤ) (h : 5 ∣ a * m^3 + b * m^2 + c * m + d)
    (h' : ¬5 ∣ d) : ∃ n : ℤ, 5 ∣ d * n^3 + c * n^2 + b * n + a := by
  have h1 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
    by_contra h1 
    push_neg at h1 
    have h2 : m % 5 = 0 := by 
      omega 
    have h3 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by 
      omega 
    simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2] at h3 
    have h4 : d % 5 = 0 := by 
      omega 
    have h5 : 5 ∣ d := by 
      omega 
    contradiction 
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- case m % 5 = 1 
    use 1 
    have h2 : (d * 1^3 + c * 1^2 + b * 1 + a) % 5 = 0 := by 
      have h_eq : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by 
        omega 
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h1] at h_eq ⊢ 
      omega 
    omega 
  · -- case m % 5 = 2 
    use 3 
    have h2 : (d * 3^3 + c * 3^2 + b * 3 + a) % 5 = 0 := by 
      have h_eq : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by 
        omega 
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h1] at h_eq ⊢ 
      omega 
    omega 
  · -- case m % 5 = 3 
    use 2 
    have h2 : (d * 2^3 + c * 2^2 + b * 2 + a) % 5 = 0 := by 
      have h_eq : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by 
        omega 
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h1] at h_eq ⊢ 
      omega 
    omega 
  · -- case m % 5 = 4 
    use 4 
    have h2 : (d * 4^3 + c * 4^2 + b * 4 + a) % 5 = 0 := by 
      have h_eq : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by 
        omega 
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h1] at h_eq ⊢ 
      omega 
    omega