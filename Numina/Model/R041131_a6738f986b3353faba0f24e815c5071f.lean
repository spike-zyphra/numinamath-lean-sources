import Mathlib

theorem algebra_193623 {a b c : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^3 + a * x^2 + b * x + c) (hroot : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ f x = 0 ∧ f y = 0 ∧ f z = 0 ∧ x * y * z = x + y + z + 2 ∧ x^2 + y^2 + z^2 = 10 ∧ x^3 + y^3 + z^3 = 6) : 
    a = 0 ∧ b = -5 ∧ c = -2 := by
  rcases hroot with ⟨x, y, z, hxy, hyz, hzx, hx, hy, hz, h1, h2, h3⟩
  have eq_x : x^3 + a * x^2 + b * x + c = 0 := by 
    rw [hf] at hx
    simpa using hx
  have eq_y : y^3 + a * y^2 + b * y + c = 0 := by 
    rw [hf] at hy
    simpa using hy
  have eq_z : z^3 + a * z^2 + b * z + c = 0 := by 
    rw [hf] at hz
    simpa using hz
  have eq4 : (x - y) * (x^2 + x * y + y^2 + a * (x + y) + b) = 0 := by
    nlinarith 
  have eq5 : x^2 + x * y + y^2 + a * (x + y) + b = 0 := by 
    apply (mul_left_inj' (sub_ne_zero.mpr hxy)).mp 
    linarith
  have eq6 : (y - z) * (y^2 + y * z + z^2 + a * (y + z) + b) = 0 := by 
    nlinarith 
  have eq7 : y^2 + y * z + z^2 + a * (y + z) + b = 0 := by 
    apply (mul_left_inj' (sub_ne_zero.mpr hyz)).mp 
    linarith
  have eq8 : (x - z) * (x + y + z + a) = 0 := by 
    nlinarith [eq5, eq7]
  have heq5 : x + y + z + a = 0 := by 
    apply (mul_left_inj' (show x - z ≠ 0 by
      intro h0
      apply hzx
      linarith
    )).mp
    linarith
  -- Hence sum of roots is -a.
  have eq40 : x + y + z = -a := by linarith 
  -- Now compute eq51 and eq51 about products.
  have eq51 : (x * y + y * z + z * x) = b := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
      intro h
      apply hxy
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by 
      intro h
      apply hyz
      linarith
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by 
      intro h
      apply hzx
      linarith
    )] 
  have h40 : x * y * z = x + y + z + 2 := by 
    linarith [h1] 
  have h51 : x^3 + y^3 + z^3 = (x + y + z)^3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by ring 
  rw [show x * y + y * z + z * x = b by linarith [eq51]] at h51 
  rw [show x + y + z = -a by linarith [eq40]] at h51 
  rw [show x * y * z = x + y + z + 2 by linarith [h1]] at h51 
  -- Now solving of coefficients.
  have h80 : a = 0 := by 
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
      intro h
      apply hxy
      linarith
    ), sq_pos_of_ne_zero (show (y - z) ≠ 0 by 
      intro h
      apply hyz
      linarith
    ), sq_pos_of_ne_zero (show (z - x) ≠ 0 by 
      intro h
      apply hzx
      linarith
    )] 
  have h20 : b = -5 := by 
    rw [h80] at eq40 
    nlinarith 
  have h30 : c = -2 := by 
    rw [h80] at eq40 
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
      intro h
      apply hxy
      linarith
    ), sq_pos_of_ne_zero (show (y - z) ≠ 0 by 
      intro h
      apply hyz
      linarith
    ), sq_pos_of_ne_zero (show (z - x) ≠ 0 by 
      intro h
      apply hzx
      linarith
    )] 
  exact ⟨h80, h20, h30⟩