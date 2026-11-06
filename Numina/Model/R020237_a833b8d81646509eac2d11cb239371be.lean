import Mathlib

theorem algebra_113475 {x y : ℕ} (h : (7 * x - 5 * y - 3 : ℚ) / (3 * x + 9 * y - 15) = 1 / 5) :
    (16 * x - 17 * y) ^ 2015 = 0 := by
  have h1 : (3 * x + 9 * y - 15 : ℚ) ≠ 0 := by
    by_contra h1
    rw [h1] at h
    norm_num at h

  have h2 : (7 * x - 5 * y - 3 : ℚ) / (3 * x + 9 * y - 15) = (1 / 5 : ℚ) := by 
    simpa using h
  
  have h3 : (7 * x - 5 * y - 3 : ℚ) * (5 : ℚ) = (3 * x + 9 * y - 15 : ℚ) * (1 : ℚ) := by
    field_simp [h1] at h2 ⊢
    linarith
  
  have eq1 : (35 * (x : ℚ) - 25 * (y : ℚ) - 15) = (3 * (x : ℚ) + 9 * (y : ℚ) - 15) := by 
    linarith [h3]

  have eq2 : (32 * (x : ℚ) ) = (34 * (y : ℚ) ) := by
    linarith [eq1]

  have eq3 : (16 * (x : ℚ) ) = (17 * (y : ℚ) ) := by
    linarith [eq2]

  have eq4 : (16 * x : ℕ) = (17 * y : ℕ) := by 
    exact_mod_cast eq3

  have eq5 : 16 * x = 17 * y := by 
    exact_mod_cast eq4

  have eq6 : 16 * x - 17 * y = 0 := by 
    omega

  calc
    (16 * x - 17 * y) ^ 2015 = (0) ^ 2015 := by rw [eq6]
    _ = 0 := by norm_num