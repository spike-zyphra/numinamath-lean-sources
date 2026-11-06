import Mathlib

theorem algebra_255658 {x y z : ℝ} (hd1 : x+y≠0) (hd2 : y+z≠0) (hd3 : z+x≠0) (h1 : x * y / (x + y) = 1 / 3) (h2 : y * z / (y + z) = 1 / 4) (h3 : z * x / (z + x) = 1 / 5) : x = 1 / 2 ∧ y = 1 ∧ z = 1 / 3 := by
  have eq1 : 3 * (x * y) = x + y := by
    have h11 : x + y ≠ 0 := hd1
    have eq1 : x * y / (x + y) = 1 / 3 := h1
    have eq2 : x * y = (1 / 3) * (x + y) := by
      field_simp [h11] at eq1 ⊢
      linarith
    linarith [eq2]
  -- Convert h2 to the form without denominator
  have eq2 : 4 * (y * z) = y + z := by
    have h22 : y + z ≠ 0 := hd2
    have eq2 : y * z / (y + z) = 1 / 4 := h2
    have eq3 : y * z = (1 / 4) * (y + z) := by
      field_simp [h22] at eq2 ⊢
      linarith
    linarith [eq3]
  -- Convert h3 to the form without denominator
  have eq3 : 5 * (z * x) = z + x := by
    have h33 : z + x ≠ 0 := hd3
    have eq3 : z * x / (z + x) = 1 / 5 := h3
    have eq4 : z * x = (1 / 5) * (z + x) := by
      field_simp [h33] at eq3 ⊢
      linarith
    linarith [eq4]
  -- Prove that y ≠ 0
  have hy1 : y ≠ 0 := by
    by_contra h
    have h4 : y = 0 := by linarith
    rw [h4] at eq1 
    have h5 : 3 * (x * (0 : ℝ)) = x + (0 : ℝ) := by linarith 
    simp at h5 
    have h6 : x = 0 := by linarith 
    have h7 : x + y = 0 := by 
      linarith 
    contradiction
  -- Prove that y = 1
  have hy2 : y = 1 := by
    -- Express x in terms of y from eq1
    have hx : x = y / (3 * y - 1) := by 
      have hy3 : 3 * y - 1 ≠ 0 := by
        by_contra h 
        have h4 : 3 * y - 1 = 0 := by linarith 
        have h5 : y = 1 / 3 := by linarith 
        rw [h5] at eq1 
        nlinarith 
      have hx1 : 3 * (x * y) = x + y := by linarith [eq1]
      have hx2 : x * (3 * y - 1) = y := by
        nlinarith 
      field_simp [(show 3 * y - 1 ≠ 0 from hy3)]
      linarith 
    -- Express z in terms of y from eq2
    have hz : z = y / (4 * y - 1) := by 
      have hy4 : 4 * y - 1 ≠ 0 := by 
        by_contra h 
        have h5 : 4 * y - 1 = 0 := by linarith 
        have h6 : y = 1 / 4 := by linarith 
        rw [h6] at eq2 
        nlinarith 
      have hz1 : 4 * (y * z) = y + z := by linarith [eq2]
      have hz2 : z * (4 * y - 1) = y := by 
        nlinarith 
      field_simp [(show 4 * y - 1 ≠ 0 from hy4)]
      linarith 
    -- Substitute x and z into eq3
    have eq4 : 5 * (z * x) = z + x := by linarith [eq3]
    rw [show x = y / (3 * y - 1) by linarith [hx]] at eq4 
    rw [show z = y / (4 * y - 1) by linarith [hz]] at eq4 
    -- Simplify the equation to solve for y
    have : 5 * ((y / (4 * y - 1) ) * (y / (3 * y - 1) )) = (y / (4 * y - 1) ) + (y / (3 * y - 1) ) := by
      nlinarith 
    have hy5 : y = 1 := by
      apply (mul_left_inj' (show y ≠ 0 by exact hy1)).mp
      field_simp [(show 4 * y - 1 ≠ 0 by
        by_contra h 
        have h5 : 4 * y - 1 = 0 := by linarith 
        have h6 : y = 1 / 4 := by linarith 
        rw [h6] at eq2 
        nlinarith 
      ), (show 3 * y - 1 ≠ 0 by
        by_contra h 
        have h4 : 3 * y - 1 = 0 := by linarith 
        have h5 : y = 1 / 3 := by linarith 
        rw [h5] at eq1 
        nlinarith 
      )] at this 
      nlinarith 
      all_goals nlinarith 
    exact_mod_cast hy5 
  -- Solve for x using y = 1
  have hx1 : x = 1 / 2 := by 
    rw [show y = 1 by linarith [hy2] ] at eq1 
    nlinarith 
  -- Solve for z using y = 1
  have hz1 : z = 1 / 3 := by 
    rw [show y = 1 by linarith [hy2] ] at eq2 
    nlinarith 
  exact ⟨hx1, hy2, hz1⟩