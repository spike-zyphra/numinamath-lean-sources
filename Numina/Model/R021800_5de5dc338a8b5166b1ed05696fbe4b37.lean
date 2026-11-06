import Mathlib

theorem algebra_211171 {P : ℝ → ℝ} (hP : ∃ a b c d : ℝ, P = fun x => a*x^3 + b*x^2 + c*x + d)
    (hP1 : P (-3) = 1) (hP2 : deriv P (-3) = 1) (hP3 : iteratedDeriv 2 P (-3) = 1)
    (hP4 : iteratedDeriv 3 P (-3) = 1) :
    P 0 = 13 := by
  rcases hP with ⟨a, b, c, d, hP'⟩
  have eq1 : P (-3) = a * (-3) ^ 3 + b * (-3) ^ 2 + c * (-3) + d := by 
    rw [hP']
    all_goals norm_num 
    all_goals ring 
  -- Express P(0)
  have eq5 : P 0 = d := by 
    rw [hP']
    norm_num
    all_goals ring 
  have eq6 : deriv P (-3) = 3 * a * (-3) ^ 2 + 2 * b * (-3) + c := by
    rw [hP']
    simp [deriv_pow, deriv_add, deriv_const, mul_comm c, mul_assoc]
    all_goals norm_num 
    all_goals ring_nf
    all_goals norm_num [mul_add, mul_assoc]
  -- Compute the second derivative 
  have eq8 : iteratedDeriv 2 P (-3) = 6 * a * (-3) + 2 * b := by
    have eq9 : iteratedDeriv 2 P (-3) = deriv (deriv P) (-3) := by 
      simp [iteratedDeriv_succ]
      <;> rfl 
    rw [eq9]
    have hP'_deriv : deriv P = fun x => 3 * a * x ^ 2 + 2 * b * x + c := by 
      funext x 
      rw [hP']
      simp [deriv_pow, deriv_add, deriv_const, mul_comm c, mul_assoc]
      all_goals ring_nf 
      all_goals norm_num [mul_add, mul_assoc]
      all_goals ring 
      all_goals norm_num
      all_goals ring 
    rw [hP'_deriv]
    simp [deriv_pow, deriv_add, deriv_const, mul_comm (2 * b), mul_assoc]
    all_goals norm_num 
    all_goals ring_nf 
    all_goals norm_num [mul_add, mul_assoc]
  -- Compute the third derivative
  have eq10 : iteratedDeriv 3 P (-3) = 6 * a := by 
    have eq11 : iteratedDeriv 3 P (-3) = deriv (iteratedDeriv 2 P) (-3) := by 
      simp [iteratedDeriv_succ]
      <;> rfl 
    rw [eq11]
    have hP'_deriv_2 : iteratedDeriv 2 P = fun x => 6 * a * x + 2 * b := by 
      funext x
      have eq17 : iteratedDeriv 2 P x = deriv (deriv P) x := by 
        simp [iteratedDeriv_succ]
        <;> rfl 
      have eq18 : deriv P = fun x => 3 * a * x ^ 2 + 2 * b * x + c := by 
        funext x 
        rw [hP']
        simp [deriv_pow, deriv_add, deriv_const, mul_comm c, mul_assoc]
        all_goals ring_nf 
        all_goals norm_num [mul_add, mul_assoc]
        all_goals ring 
      rw [eq17, eq18]
      simp [deriv_pow, deriv_add, deriv_const, mul_comm (2 * b), mul_assoc]
      all_goals ring_nf 
      all_goals norm_num [mul_add, mul_assoc]
      all_goals ring 
      all_goals norm_num 
    rw [hP'_deriv_2]
    simp [deriv_add, deriv_const, deriv_id', mul_comm (6 * a)]
    all_goals norm_num 
    all_goals ring_nf 
    all_goals norm_num [mul_add, mul_assoc]
  -- Now express the given conditions in terms of coefficients
  have eq6' : a * (-3) ^ 3 + b * (-3) ^ 2 + c * (-3) + d = 1 := by
    linarith [hP1, eq1]
  -- Second equation
  have eq7' : 3 * a * (-3) ^ 2 + 2 * b * (-3) + c = 1 := by 
    linarith [hP2, eq6]
  -- Third equation
  have eq8' : 6 * a * (-3) + 2 * b = 1 := by 
    linarith [hP3, eq8]
  -- Fourth equation 
  have eq9' : 6 * a = 1 := by 
    linarith [hP4, eq10]
  -- Solving the linear system
  have ha1 : a = 1 / 6 := by linarith
  have hb1 : b = 2 := by 
    rw [ha1] at eq8'
    linarith 
  have hc1 : c = 17 / 2 := by 
    rw [ha1, hb1] at eq7'
    linarith 
  have hd1 : d = 13 := by 
    rw [ha1, hb1, hc1] at eq6'
    linarith 
  -- Final computation
  rw [eq5]
  all_goals norm_num [hd1]
  all_goals linarith
  all_goals norm_num 
  all_goals linarith 
  all_goals norm_num
  all_goals linarith