import Mathlib

theorem algebra_318821 {x y z a b c : ℝ} (hxy : x * y = a) (hxz : x * z = b) (hyz : y * z = c)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    x ^ 2 + y ^ 2 + z ^ 2 = ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) / (a * b * c) := by

  have h1 : x ≠ 0 := by
    by_contra h
    have hxy' : x * y = 0 := by
      rw [h]
      norm_num
    have h_eq : a = 0 := by
      linarith [hxy, hxy']
    contradiction
  have h2 : y ≠ 0 := by
    by_contra h
    have hxy' : x * y = 0 := by
      rw [h]
      norm_num
    have h_eq : a = 0 := by
      linarith [hxy, hxy']
    contradiction
  have h3 : z ≠ 0 := by
    by_contra h
    have hxz' : x * z = 0 := by
      rw [h]
      norm_num
    have h_eq : b = 0 := by
      linarith [hxz, hxz']
    contradiction

  have h4 : y ^ 2 = a * c / b := by
    have eq1 : x = a / y := by
      field_simp [h2]
      linarith
    have eq2 : z = c / y := by
      field_simp [h2]
      linarith
    rw [eq1, eq2] at hxz
    field_simp [h2, hb, ha, hc] at hxz ⊢
    linarith

  have hx5 : x ^ 2 = a * b / c := by 
    have h5 : x = a / y := by 
      field_simp [h2]
      linarith
    have h6 : x ^ 2 = (a / y) ^ 2 := by 
      rw [h5]
    have h7 : (a / y) ^ 2 = a * b / c := by
      have h8 : y ^ 2 = a * c / b := h4
      have h9 : (a / y) ^ 2 = a ^ 2 / (y ^ 2) := by 
        field_simp [h2]
      rw [h9, h8]
      field_simp [ha, hb, hc]
      <;> ring
    linarith [h6, h7]

  have hz5 : z ^ 2 = b * c / a := by
    have h10 : z = b / x := by 
      have eq3 : x * z = b := hxz
      field_simp [h1] at eq3 ⊢
      linarith
    have h11 : z ^ 2 = (b / x) ^ 2 := by 
      rw [h10]
    have h12 : (b / x) ^ 2 = b * c / a := by
      have h13 : x ^ 2 = a * b / c := hx5
      have h14 : (b / x) ^ 2 = b ^ 2 / (x ^ 2) := by 
        field_simp [h1]
      rw [h14, h13]
      field_simp [ha, hb, hc]
      <;> ring
    linarith [h11, h12]

  have h5 : x ^ 2 + y ^ 2 + z ^ 2 = a * b / c + a * c / b + b * c / a := by
    linarith [hx5, h4, hz5]

  rw [h5]
  have eq3 : a * b / c + a * c / b + b * c / a = ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) / (a * b * c) := by
    field_simp [ha, hb, hc]
    <;> ring
  rw [eq3]