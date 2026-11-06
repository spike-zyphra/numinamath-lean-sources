import Mathlib

theorem algebra_96237 {F : ℕ → ℝ}
    (hF : F 1 = 1 ∧ F 2 = 1 ∧ F 3 = 1)
    (hFn : ∀ n ≥ 3, F (n + 1) = (F n * F (n - 1) + 1) / F (n - 2)) :
    F 6 = 7 := by
  have h1 : F 1 = 1 := hF.1
  have h2 : F 2 = 1 := hF.2.1
  have h3 : F 3 = 1 := hF.2.2

  have h4 : F 4 = 2 := by
    have h4_eq : F 4 = (F 3 * F 2 + 1) / F 1 := by 
      specialize hFn 3 (by norm_num)
      simpa using hFn
    rw [h4_eq]
    rw [h1, h2, h3]
    norm_num
  
  have h5 : F 5 = 3 := by 
    have h5_eq : F 5 = (F 4 * F 3 + 1) / F 2 := by 
      specialize hFn 4 (by norm_num)
      simpa using hFn
    rw [h5_eq]
    rw [h4, h3, h2]
    norm_num

  have h6_eq : F 6 = (F 5 * F 4 + 1) / F 3 := by 
    specialize hFn 5 (by norm_num)
    simpa using hFn
  
  rw [h6_eq]
  rw [h5, h4, h3]
  norm_num