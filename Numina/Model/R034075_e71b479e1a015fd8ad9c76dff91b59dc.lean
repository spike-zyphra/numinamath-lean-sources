import Mathlib

theorem algebra_254662 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x + 6) / y + 13 / (x * y) = (4 - y) / x ↔ (x, y) = (-3, 2) := by
  constructor
  · -- Forward direction: given the equation, prove the pair is (-3, 2)
    intro h
    have eq1 : x^2 + 6 * x + 13 = 4 * y - y^2 := by
      have eq2 : (x + 6) / y + 13 / (x * y) = (4 - y) / x := h
      have eq3 : x ^ 2 + 6 * x + 13 = (4 - y) * y := by
        have eq3' : (x + 6) / y + 13 / (x * y) = (4 - y) / x := h
        have eq4 : (x + 6) / y + 13 / (x * y) = ((x + 6) * (x ) + 13) / (x * y ) := by 
          field_simp [hx, hy]
          <;> ring
        have eq5 : (4 - y) / x = ((4 - y) * y ) / (x * y ) := by
          field_simp [hx, hy]
          <;> ring
        rw [eq4, eq5] at eq3'
        have eq6 : x * y ≠ 0 := by
          apply mul_ne_zero
          · exact hx
          · exact hy
        have eq7 : ((x + 6) * (x ) + 13 ) = ((4 - y) * y ) := by
          have h1 : ((x + 6) * (x ) + 13 ) / (x * y ) = ((4 - y) * y ) / (x * y ) := by
            simpa using eq3'
          have h2 : ((x + 6) * (x ) + 13 ) = ((4 - y) * y ) := by
            have h3 : x * y ≠ 0 := eq6
            field_simp [h3] at h1 ⊢
            <;> linarith
          linarith
        linarith
      linarith
    have eq2 : (x + 3) ^ 2 + (y - 2) ^ 2 = 0 := by
      nlinarith
    have hx2 : (x + 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 2)]
    
    have hy2 : (y - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 2)]
    have hx3 : x + 3 = 0 := by
      rwa [sq_eq_zero_iff] at hx2
    have hy3 : y - 2 = 0 := by
      rwa [sq_eq_zero_iff] at hy2
    have hx4 : x = -3 := by linarith
    have hy4 : y = 2 := by linarith
    simp [hx4, hy4]
  · -- Reverse direction: given the pair is (-3, 2), prove the equation
    rintro ⟨rfl, rfl⟩
    norm_num