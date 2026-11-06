import Mathlib
open Real

/- PROBLEM: The shortest distances between an interior diagonal of a rectangular parallelepiped, P, 
and the edges it does not meet are 2*√5, 30 / √13 and 15 / √10. Determine the volume of P. -/
theorem geometry_94936 
  (a b c : ℝ) 
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
  (h1 : a * b / (sqrt (a^2 + b^2)) = 15 / sqrt 10) 
  (h2 : a * c / (sqrt (a^2 + c^2)) = 30 / (sqrt 13)) 
  (h3 : b * c / (sqrt (b^2 + c^2)) = 10 / (sqrt 5)) : 
  a * b * c = 750 := by {


  --Some trivial auxiliary statements
  have ha2ge : a ^ 2 ≥ 0 := by { rw [ge_iff_le]; exact sq_nonneg a }
  have hb2ge : b ^ 2 ≥ 0 := by { rw [ge_iff_le]; exact sq_nonneg b }
  have hc2ge : c ^ 2 ≥ 0 := by { rw [ge_iff_le]; exact sq_nonneg c }

  -- Rewrite the hypotheses, removing the square roots and then rearranging the equations to become linear equations
  -- in 1/a^2, 1/b^2, 1/c^2
  have h1' := congrArg (λ x : ℝ ↦ x^2) h1 
  simp at h1' 
  rw [div_pow,Real.sq_sqrt,div_pow,Real.sq_sqrt] at h1'

  have h2' := congrArg (λ x : ℝ ↦ x^2) h2 
  simp at h2' 
  rw [div_pow,Real.sq_sqrt,div_pow,Real.sq_sqrt] at h2'

  have h3' := congrArg (λ x : ℝ ↦ x^2) h3 
  simp at h3' 
  rw [div_pow,Real.sq_sqrt,div_pow,Real.sq_sqrt] at h3'

  rw [←one_div_div,mul_pow,add_div,div_mul_cancel_left₀,div_mul_cancel_right₀] at h1'
  rw [←one_div_div,mul_pow,add_div,div_mul_cancel_left₀,div_mul_cancel_right₀] at h2'
  rw [←one_div_div,mul_pow,add_div,div_mul_cancel_left₀,div_mul_cancel_right₀] at h3'

  let a' := (a ^ 2)⁻¹
  let b' := (b ^ 2)⁻¹
  let c' := (c ^ 2)⁻¹

  have h1'' : a' + b' = 10 / 15^2 := by {
    unfold a' 
    unfold b'
    field_simp
    field_simp at h1'
    symm
    rw [mul_comm,mul_comm (a^2) (b^2),mul_comm (b^2 + a^2) (15^2),add_comm,h1']
  }

  have h2'' : a' + c' = 13 / 30^2 := by {
    unfold a' 
    unfold c'
    field_simp
    field_simp at h2'
    symm
    rw [mul_comm,mul_comm (a^2) (c^2),mul_comm (c^2 + a^2) (30^2),add_comm,h2']
  }

  have h3'' : b' + c' = 5 / 10^2 := by {
    unfold b' 
    unfold c'
    field_simp
    field_simp at h3'
    symm
    rw [mul_comm,mul_comm (b^2) (c^2),mul_comm (c^2 + b^2) (10^2),add_comm,h3']
  }

  -- Solve those linear equations

  have ha' : a' = 1 / 15^2 := by {
    calc a' = 2 * a' / 2 := by simp
      _ = ((a' + b') + (a' + c') - (b' + c')) / 2 := by ring
      _ = (10 / 15^2 + (13 / 30^2) - 5 / 10^2) / 2 := by rw [h1'',h2'',h3'']
      _ = 1 / 15^2 := by norm_num
  }

  have hb' : b' = 1 / 5^2 := by {
    calc b' = 2 * b' / 2 := by simp
      _ = ((a' + b') - (a' + c') + (b' + c')) / 2 := by ring
      _ = (10 / 15^2 - (13 / 30^2) + 5 / 10^2) / 2 := by rw [h1'',h2'',h3'']
      _ = 1 / 5^2 := by norm_num
  }

  have hc' : c' = 1 / 10^2 := by {
    calc c' = 2 * c' / 2 := by simp
      _ = (-(a' + b') + (a' + c') + (b' + c')) / 2 := by ring
      _ = (-(10 / 15^2) + (13 / 30^2) + 5 / 10^2) / 2 := by rw [h1'',h2'',h3'']
      _ = 1 / 10^2 := by norm_num
  }

  -- Transform those solutions into solutions for the original variables, the side lengths of the parallelepiped

  have ha'' : a = 15 := by {
    unfold a' at ha'
    simp at ha'
    rw [sq_eq_sq_iff_abs_eq_abs,abs_of_nonneg _] at ha'
    simp at ha'
    exact ha'
    linarith
  }

  have hb'' : b = 5 := by {
    unfold b' at hb'
    simp at hb'
    rw [sq_eq_sq_iff_abs_eq_abs,abs_of_nonneg _] at hb'
    simp at hb'
    exact hb'
    linarith
  }

  have hc'' : c = 10 := by {
    unfold c' at hc'
    simp at hc'
    rw [sq_eq_sq_iff_abs_eq_abs,abs_of_nonneg _] at hc'
    simp at hc'
    exact hc'
    linarith
  }

  -- Evaluate the volume using the side lengths

  rw [ha'',hb'',hc'']

  -- Verify that various assumptions in the results used are satisfied (variables non-zero / positive)

  norm_num
  norm_num
  linarith
  intro hb2
  rw [sq_eq_zero_iff] at hb2
  linarith
  intro hc2
  rw [sq_eq_zero_iff] at hc2
  linarith
  intro ha2
  rw [sq_eq_zero_iff] at ha2
  linarith
  intro hb2
  rw [sq_eq_zero_iff] at hb2
  linarith
  intro ha2
  rw [sq_eq_zero_iff] at ha2
  linarith
  norm_num
  linarith
  linarith
  linarith
  norm_num
  linarith
}