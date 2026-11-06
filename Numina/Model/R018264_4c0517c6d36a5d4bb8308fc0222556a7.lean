import Mathlib

theorem algebra_304252 {x y z k : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 1 / x^3 = 8 / y^3) (h2 : 8 / y^3 = 27 / z^3) (h3 : 27 / z^3 = k / (x + y + z)^3) :
    k = 216 := by
  have eq1 : y^3 = 8 * x^3 := by 
    have hne1 : x^3 ≠ 0 := by
      have hx1 : x ≠ 0 := by linarith
      intro h
      have h4 : x = 0 := by 
        have h5 : x^3 = 0 := by 
          nlinarith 
        have h6 : x = 0 := by 
          have h7 : x^3 = 0 := h5 
          simp at h7 ⊢ 
          <;> nlinarith 
        exact h6 
      linarith [hx, h4]
    have hne2 : y^3 ≠ 0 := by
      have hy1 : y ≠ 0 := by linarith
      intro h
      have h4 : y = 0 := by 
        have h5 : y^3 = 0 := by
          nlinarith 
        have h6 : y = 0 := by 
          have h7 : y^3 = 0 := h5 
          simp at h7 ⊢ 
          <;> nlinarith 
        exact h6 
      linarith [hy, h4]
    field_simp [hne1, hne2] at h1
    nlinarith
  have eq2 : y = 2 * x := by 
    have h4 : y^3 - 8 * x^3 = 0 := by linarith 
    have h5 : y^3 - 8 * x^3 = (y - 2 * x) * (y^2 + 2 * x * y + 4 * x^2) := by nlinarith
    rw [h5] at h4 
    cases' (mul_eq_zero.1 h4) with h6 h7 
    · linarith 
    · -- \(y^{2} + 2xy + 4x^{2} = 0\)
      nlinarith [sq_nonneg (y + x), sq_nonneg (y - 2 * x), sq_nonneg (x - y)]
  -- Now we need to manipulate h2 using the value of y
  have eq3 : 8 * z^3 = 27 * y^3 := by 
    have hne1 : y^3 ≠ 0 := by 
      have hy1 : y ≠ 0 := by linarith 
      intro h 
      have h4 : y = 0 := by 
        have h5 : y^3 = 0 := by
          nlinarith 
        have h6 : y = 0 := by 
          have h7 : y^3 = 0 := h5 
          simp at h7 ⊢ 
          <;> nlinarith 
        exact h6 
      linarith [hy, h4]
    have hne2 : z^3 ≠ 0 := by
      have hz1 : z ≠ 0 := by linarith 
      intro h 
      have h4 : z = 0 := by 
        have h5 : z^3 = 0 := by
          nlinarith 
        have h6 : z = 0 := by 
          have h7 : z^3 = 0 := h5 
          simp at h7 ⊢ 
          <;> nlinarith 
        exact h6 
      linarith [hz, h4]
    field_simp [hne1, hne2] at h2 
    nlinarith 
  have eq4 : z = 3 * x := by 
    rw [show y = 2 * x by linarith [eq2]] at eq3 
    have h8 : 8 * z^3 = 27 * (2 * x) ^3 := by 
      linarith 
    have h9 : 8 * z^3 = 216 * x^3 := by 
      nlinarith [h8]
    have h10 : z^3 = 27 * x^3 := by 
      nlinarith 
    have h11 : z^3 - 27 * x^3 = 0 := by linarith 
    have h12 : z^3 - 27 * x^3 = (z - 3 * x) * (z^2 + 3 * x * z + 9 * x^2) := by 
      nlinarith 
    rw [h12] at h11 
    cases' (mul_eq_zero.1 h11) with h13 h14 
    · linarith 
    · -- \(z^{2} + 3xz + 9x^{2} = 0\)
      nlinarith [sq_nonneg (z + x), sq_nonneg (z - 3 * x), sq_nonneg (x - z)]
  -- Now compute x + y + z
  have eq5 : x + y + z = 6 * x := by 
    have hy1 : y = 2 * x := by linarith [eq2] 
    have hz1 : z = 3 * x := by linarith [eq4] 
    nlinarith [hy1, hz1]
  -- Now compute z^3 and (x + y + z)^3
  have eq6 : z^3 = 27 * x^3 := by 
    have hz1 : z = 3 * x := by linarith [eq4] 
    rw [hz1] 
    nlinarith 
  have eq7 : (x + y + z)^3 = 216 * x^3 := by 
    rw [eq5] 
    nlinarith [sq_nonneg (x), sq_pos_of_pos hx]
  have hne1 : z^3 ≠ 0 := by 
    have hz1 : z ≠ 0 := by linarith 
    intro h 
    have h4 : z = 0 := by 
      have h5 : z^3 = 0 := by 
        nlinarith 
      have h6 : z = 0 := by 
        have h7 : z^3 = 0 := h5 
        simp at h7 ⊢ 
        <;> nlinarith 
      exact h6 
    linarith [hz, h4]
  have hne2 : (x + y + z)^3 ≠ 0 := by 
    intro h
    have h10 : (x + y + z) ^3 = 0 := by 
      nlinarith 
    have h11 : x + y + z = 0 := by 
      have h12 : (x + y + z) ^3 = 0 := h10 
      have h13 : x + y + z = 0 := by 
        have h14 : (x + y + z)^3 = 0 := h12 
        simp at h14 ⊢ 
        <;> nlinarith 
      exact h13 
    -- Now we know x + y + z = 0, contradiction.
    have h14 : x = 0 := by 
      nlinarith [h11, eq5] 
    -- Contradiction with hx : 0 < x
    nlinarith [hx, h14]
  have eq8 : 27 * ((x + y + z) ^3) = k * (z^3) := by 
    have hne1_z3 : z^3 ≠ 0 := hne1 
    have hne2_xP : (x + y + z)^3 ≠ 0 := hne2 
    field_simp [hne1_z3, hne2_xP] at h3 ⊢ 
    nlinarith 
  rw [eq7, eq6] at eq8 
  have hx2 : x^3 > 0 := by 
    apply pow_pos 
    exact hx 
  have eq9 : 27 * (216 * x^3) = k * (27 * x^3) := by linarith [eq8]
  have hx3 : x^3 ≠ 0 := by 
    linarith [hx2] 
  have eq10 : 27 * 216 * x^3 = 27 * k * x^3 := by 
    linarith [eq9]
  have eq11 : 27 * 216 * x^3 - 27 * k * x^3 = 0 := by linarith 
  have factored : 27 * (216 * x^3 - k * x^3) = 0 := by 
    linarith [eq11]
  have eq12 : 216 * x^3 - k * x^3 = 0 := by 
    have hne : (27 : ℝ) ≠ 0 := by norm_num 
    apply (mul_left_inj' hne).mp 
    linarith [factored]
  have eq13 : (216 - k) * x^3 = 0 := by 
    nlinarith [eq12]
  cases' (mul_eq_zero.1 eq13) with eq14 eq15 
  · -- If $216 - k = 0$ then $k = 216$ which proves the theorem 
    linarith 
  · -- $x^3 = 0$
    nlinarith [hx2, eq15]