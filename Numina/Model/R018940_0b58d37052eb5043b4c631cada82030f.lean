import Mathlib

theorem number_theory_115544 (x y z : ℤ) : ¬(x*y*(x-y) + y*z*(y-z) + z*x*(z-x) = -1) := by 
  intro h 
  have eq1 : (x * y * (x - y) + y * z * (y - z) + z * x * (z - x)) % 2 = 0 := by
    have h11 : x * y * (x - y) % 2 = 0 := by
      have h111 : x % 2 = 0 ∨ x % 2 = 1 := by 
        omega 
      have h112 : y % 2 = 0 ∨ y % 2 = 1 := by 
        omega 
      rcases h111 with (h111 | h111) <;> rcases h112 with (h112 | h112) <;> 
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h111, h112, pow_two] 
    have h112 : (y * z * (y - z)) % 2 = 0 := by 
      have h1111 : y % 2 = 0 ∨ y % 2 = 1 := by 
        omega 
      have h1112 : z % 2 = 0 ∨ z % 2 = 1 := by 
        omega 
      rcases h1111 with (h1111 | h1111) <;> rcases h1112 with (h1112 | h1112) <;> 
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h1111, h1112, pow_two] 
    have h113 : (z * x * (z - x)) % 2 = 0 := by 
      have h1111 : z % 2 = 0 ∨ z % 2 = 1 := by 
        omega 
      have h1112 : x % 2 = 0 ∨ x % 2 = 1 := by 
        omega 
      rcases h1111 with (h1111 | h1111) <;> rcases h1112 with (h1112 | h1112) <;> 
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h1111, h1112, pow_two] 
    omega 
  have eq2 : (-1 : ℤ) % 2 = 1 := by 
    omega 
  have h_eq1 : (x * y * (x - y) + y * z * (y - z) + z * x * (z - x)) % 2 = (-1) % 2 := by 
    omega 
  rw [eq2] at h_eq1 
  omega