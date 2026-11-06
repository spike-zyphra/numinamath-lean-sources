import Mathlib

theorem algebra_303452 {x y z u : ℝ} (h₀ : y + z + u ≠ 0) (h₁ :  z + u + x≠ 0)
    (h₂ :  u + x + y≠ 0) (h₃ : x + y + z≠ 0) (h₄ : x / (y + z + u) = y / (z + u + x))
    (h₅ : y / (z + u + x) = z / (u + x + y)) (h₆ : z / (u + x + y) = u / (x + y + z)) (hn1 : x+y≠ 0)(hn2 : y+z≠ 0)(hn3 : z+u≠ 0)(hn4 : u+x≠ 0):
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = 4 ∨
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = -4 := by

  have eq1 : x * (z + u + x) = y * (y + z + u) := by
    field_simp [h₀, h₁] at h₄
    linarith

  have eq2 : y * (u + x + y) = z * (z + u + x) := by
    field_simp [h₁, h₂] at h₅
    linarith

  have eq3 : z * (x + y + z) = u * (u + x + y) := by
    field_simp [h₂, h₃] at h₆
    linarith
  
  have h8 : x + y + z + u = 0 ∨ x = y ∧ y = z ∧ z = u := by 
    by_cases h : x + y + z + u = 0
    · 
      tauto
    · 
      have h9 : x = y := by
        apply (mul_left_inj' h).mp
        nlinarith [eq1, eq2, eq3, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - u), sq_nonneg (x - z), sq_nonneg (x - u), sq_nonneg (y - u)]
      have h11 : y = z := by
        apply (mul_left_inj' h).mp
        nlinarith [eq1, eq2, eq3, sq_nonneg (y - z), sq_nonneg (x - z), sq_nonneg (x - u), sq_nonneg (y - u), sq_nonneg (x - y), sq_nonneg (z - u)]
      have h12 : z = u := by
        apply (mul_left_inj' h).mp
        nlinarith [eq1, eq2, eq3, sq_nonneg (z - u), sq_nonneg (x - u), sq_nonneg (y - u), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
      tauto
  
  rcases h8 with h8 | h8
  · -- Case where sum is zero
    have h81 : x + y = - (z + u) := by
      nlinarith
    have h82 : y + z = - (u + x) := by
      nlinarith
    have h83 : z + u = - (x + y) := by
      nlinarith
    have h84 : u + x = - (y + z) := by
      nlinarith
    right
    have h91 : (x + y) / (z + u) = -1 := by
      have h911 : z + u ≠ 0 := by 
        exact_mod_cast hn3
      have h912 : x + y = - (z + u) := by
        linarith
      field_simp [h911]
      linarith
    have h92 : (y + z) / (u + x) = -1 := by
      have h921 : u + x ≠ 0 := by
        exact_mod_cast hn4
      have h922 : y + z = - (u + x) := by
        linarith
      field_simp [h921]
      linarith
    have h93 : (z + u) / (x + y) = -1 := by
      have h931 : x + y ≠ 0 := by
        exact_mod_cast hn1
      have h932 : z + u = - (x + y) := by
        linarith
      field_simp [h931]
      linarith
    have h94 : (u + x) / (y + z) = -1 := by
      have h941 : y + z ≠ 0 := by 
        exact_mod_cast hn2
      have h942 : u + x = - (y + z) := by 
        linarith
      field_simp [h941]
      linarith
    linarith [h91, h92, h93, h94]

  · 
    rcases h8 with ⟨hr1, hr2, hr3⟩
    left
    have h91 : (x + y) / (z + u) = 1 := by
      have h911 : z + u ≠ 0 := by 
        exact_mod_cast hn3
      have h912 : x + y = 2 * x := by
        nlinarith [hr1]
      have h913 : z + u = 2 * x := by
        nlinarith [hr1, hr2, hr3]
      field_simp [h911]
      nlinarith [h912, h913]
    have h92 : (y + z) / (u + x) = 1 := by
      have h921 : u + x ≠ 0 := by
        exact_mod_cast hn4
      have h922 : y + z = 2 * x := by
        nlinarith [hr1, hr2, hr3]
      have h923 : u + x = 2 * x := by
        nlinarith [hr1, hr3]
      field_simp [h921]
      nlinarith [h922, h923]
    have h93 : (z + u) / (x + y) = 1 := by
      have h931 : x + y ≠ 0 := by 
        exact_mod_cast hn1
      have h932 : z + u = 2 * x := by
        nlinarith [hr1, hr3]
      have h933 : x + y = 2 * x := by
        nlinarith [hr1]
      field_simp [h931]
      nlinarith [h932, h933]
    have h94 : (u + x) / (y + z) = 1 := by
      have h941 : y + z ≠ 0 := by
        exact_mod_cast hn2
      have h942 : u + x = 2 * x := by
        nlinarith [hr1, hr3]
      have h943 : y + z = 2 * x := by
        nlinarith [hr1, hr2, hr3]
      field_simp [h941]
      nlinarith [h942, h943]
    linarith [h91, h92, h93, h94]