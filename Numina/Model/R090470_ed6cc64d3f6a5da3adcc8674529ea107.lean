import Mathlib

theorem algebra_13789 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x > y)
    (h : x^2 + y^2 = 3961 * x * y / 1980) : (x + y) / (x - y) = 89 := by
  have h1 : x - y ≠ 0 := by linarith
  have h2 : x * y ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · linarith
  
  have h3 : (x + y) ^ 2 = (3961 / 1980 + 2) * (x * y) := by
    have h_eq : x^2 + y^2 = 3961 * x * y / 1980 := h
    calc 
      (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by ring
      _ = (x^2 + y^2) + 2 * (x * y) := by ring
      _ = (3961 * x * y / 1980) + 2 * (x * y) := by rw [h_eq]
      _ = (3961 / 1980 + 2) * (x * y) := by ring

  have h4 : (x - y) ^ 2 = (3961 / 1980 - 2) * (x * y) := by
    have h_eq : x^2 + y^2 = 3961 * x * y / 1980 := h
    calc
      (x - y) ^ 2 = x^2 + y^2 - 2 * (x * y) := by ring
      _ = (x^2 + y^2) - 2 * (x * y) := by ring
      _ = (3961 * x * y / 1980) - 2 * (x * y) := by rw [h_eq]
      _ = (3961 / 1980 - 2) * (x * y) := by ring
  
  have h5 : ((x + y) / (x - y)) ^ 2 = 7921 := by
    have h6 : (x - y) ≠ 0 := h1
    have h7 : x * y ≠ 0 := h2
    calc
      ((x + y) / (x - y)) ^ 2 = ((x + y) ^ 2) / ((x - y) ^ 2) := by field_simp [h6]
      _ = ( (3961 / 1980 + 2) * (x * y) ) / ( (3961 / 1980 - 2) * (x * y) ) := by rw [h3, h4]
      _ = ( (3961 / 1980 + 2) * (x * y) ) / ( (3961 / 1980 - 2) * (x * y) ) := by ring
      _ = ( (3961 / 1980 + 2) / (3961 / 1980 - 2) ) * ( (x * y) / (x * y) ) := by 
        field_simp [h6] -- h7
        <;> ring
      _ = ( (3961 / 1980 + 2) / (3961 / 1980 - 2) ) * 1 := by 
        field_simp [h7]
        <;> nlinarith
      _ = ( (3961 / 1980 + 2) / (3961 / 1980 - 2) ) := by ring
      _ = 7921 := by norm_num
  
  have h6 : (x + y) / (x - y) > 0 := by
    have h7 : x - y > 0 := by linarith
    have h8 : x + y > 0 := by linarith
    apply div_pos
    all_goals linarith

  have h7 : (x + y) / (x - y) = 89 := by 
    have h8 : ((x + y) / (x - y)) ^ 2 = 7921 := h5
    have h9 : (x + y) / (x - y) > 0 := h6
    have h10 : (x + y) / (x - y) = Real.sqrt 7921 := by 
      have h : ((x + y) / (x - y)) ^ 2 = (7921 : ℝ) := h8
      have h_pos : (x + y) / (x - y) > 0 := h9
      have : Real.sqrt (((x + y) / (x - y)) ^ 2) = Real.sqrt (7921 : ℝ) := by 
        rw [h]
      rw [Real.sqrt_sq (by linarith)] at this 
      linarith 
    have h11 : Real.sqrt 7921 = 89 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      <;> linarith 
    rw [h11] at h10 
    linarith 

  exact h7