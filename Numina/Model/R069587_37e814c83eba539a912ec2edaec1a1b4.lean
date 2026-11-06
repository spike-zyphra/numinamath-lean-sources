import Mathlib

theorem algebra_290340 (x y z : ℕ) (h : x + y + z = 235)
    (h1 : (3 / 4 : ℚ) * x = (1 / 3 : ℚ) * y) (h2 : (1 / 2 : ℚ) * y = (3 / 7 : ℚ) * z) :
    y = 90 := by
  have eq1 : (x : ℚ) + (y : ℚ) + (z : ℚ) = (235 : ℚ) := by exact_mod_cast h
  have eq2 : (3 / 4 : ℚ) * (x : ℚ) = (1 / 3 : ℚ) * (y : ℚ) := by exact_mod_cast h1
  have eq3 : (1 / 2 : ℚ) * (y : ℚ) = (3 / 7 : ℚ) * (z : ℚ) := by exact_mod_cast h2
  
  have h3 : (y : ℚ) = (9 / 4 : ℚ) * (x : ℚ) := by
    linarith [eq2]

  have h4 : (z : ℚ) = (21 / 8 : ℚ) * (x : ℚ) := by
    have hz : (z : ℚ) = (7 / 6 : ℚ) * (y : ℚ) := by
      field_simp at eq3 ⊢
      linarith
    rw [hz, h3]
    field_simp
    linarith
  
  have h5 : (x : ℚ) = 40 := by
    have eq4 : (x : ℚ) + (y : ℚ) + (z : ℚ) = (235 : ℚ) := by exact_mod_cast h
    rw [h3, h4] at eq4
    linarith
  
  have h7 : (y : ℚ) = 90 := by
    rw [h5] at h3
    norm_num at h3 ⊢
    linarith
  
  exact_mod_cast h7