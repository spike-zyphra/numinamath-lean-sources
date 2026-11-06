import Mathlib

theorem number_theory_243376 (n : ℤ) (h : ¬ 7 ∣ n) :
    7 ∣ (n^3 + 1) ∨ 7 ∣ (n^3 - 1) := by 
  have h1 : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    omega 
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1)
  · -- case n % 7 = 1 
    have h2 : (n ^ 3) % 7 = 1 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 - 1) % 7 = 0 := by 
      omega 
    right 
    omega 
  · -- case n % 7 = 2 
    have h2 : (n ^ 3) % 7 = 1 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 - 1) % 7 = 0 := by 
      omega 
    right 
    omega 
  · -- case n % 7 = 3 
    have h2 : (n ^ 3) % 7 = 6 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 + 1) % 7 = 0 := by 
      omega 
    left 
    omega 
  · -- case n % 7 = 4 
    have h2 : (n ^ 3) % 7 = 1 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 - 1) % 7 = 0 := by 
      omega 
    right 
    omega 
  · -- case n % 7 = 5 
    have h2 : (n ^ 3) % 7 = 6 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 + 1) % 7 = 0 := by 
      omega 
    left 
    omega 
  · -- case n % 7 = 6 
    have h2 : (n ^ 3) % 7 = 6 := by 
      simp [pow_three, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      <;> omega 
    have h3 : (n^3 + 1) % 7 = 0 := by 
      omega 
    left 
    omega