import Mathlib

theorem algebra_180937 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x^3 + y^3 + z^3 = 8) 
    (h2 : x^2 + y^2 + z^2 = 22) 
    (h3 : 1 / x + 1 / y + 1 / z = -z / (x * y)) :
    (x, y, z) = (3, 2, -3) ∨ (x, y, z) = (-3, 2, 3) ∨ (x, y, z) = (2, 3, -3) ∨ (x, y, z) = (2, -3, 3) := by

  have eq1 : z^2 + (x + y) * z + x * y = 0 := by
    field_simp [hx, hy, hz] at h3 ⊢
    have h4 : ((y + x) * z + x * y) * (x * y) = -(z * (x * y * z)) := by
      nlinarith [h3]
    -- Divide through `x * y` as they're non-zero
    have h5 : (x + y) * z + x * y = - z^2 := by
      apply (mul_left_inj' (mul_ne_zero hx hy)).mp
      linarith
    nlinarith
  
  have eq2 : (z + x) * (z + y) = 0 := by 
    nlinarith [eq1]

  cases' (mul_eq_zero.mp eq2) with h9 h10
  · -- Case where `z + x = 0`, so `z = -x`
    have eq3 : z = -x := by linarith 
    have eq4 : y = 2 := by 
      have h4 : y^3 = 8 := by 
        rw [show z = -x by linarith [eq3]] at h1 
        nlinarith 
      have h5 : y = 2 := by 
        have h6 : y^3 - 8 = 0 := by linarith 
        have h7 : (y - 2) * (y^2 + 2 * y + 4) = 0 := by 
          ring_nf at h6 ⊢ 
          linarith 
        cases' (mul_eq_zero.mp h7) with h8 h9 
        · linarith 
        · 
          have h10 : y^2 + 2 * y + 4 > 0 := by 
            nlinarith [sq_nonneg (y + 1)]
          nlinarith 
      linarith 
    have eq8 : x^2 = 9 := by 
      rw [show y = 2 by linarith [eq4], show z = -x by linarith [eq3]] at h2 
      nlinarith 
    have eq9 : x = 3 ∨ x = -3 := by 
      have h11 : x^2 = 9 := eq8 
      have h12 : x^2 = 3^2 := by nlinarith 
      have h13 : x = 3 ∨ x = -3 := by 
        have h4 : x^2 = 9 := eq8 
        have h5 : x^2 - 9 = 0 := by linarith 
        have h6 : (x - 3) * (x + 3) = 0 := by 
          linarith 
        cases' (mul_eq_zero.mp h6) with h7 h8 
        · left 
          linarith 
        · right 
          linarith 
      tauto 
    cases' eq9 with h17 h17
    · 
      have hx10 : x = 3 := h17 
      have h11 : z = -3 := by linarith [eq3, hx10] 
      simp [hx10, eq4, h11] 
    · 
      have hx10 : x = -3 := h17 
      have h11 : z = 3 := by linarith [eq3, hx10] 
      simp [hx10, eq4, h11] 
  · -- Case where `z + y = 0`, so `z = -y`
    have eq3 : z = -y := by linarith 
    have eq4 : x = 2 := by 
      have h4 : x^3 = 8 := by 
        rw [show z = -y by linarith [eq3]] at h1 
        nlinarith 
      have h5 : x = 2 := by 
        have h6 : x^3 - 8 = 0 := by linarith 
        have h7 : (x - 2) * (x^2 + 2 * x + 4) = 0 := by 
          ring_nf at h6 ⊢ 
          linarith 
        cases' (mul_eq_zero.mp h7) with h8 h9 
        · linarith 
        · 
          have h10 : x^2 + 2 * x + 4 > 0 := by 
            nlinarith [sq_nonneg (x + 1)]
          nlinarith 
      linarith 
    have eq8 : y^2 = 9 := by 
      rw [show x = 2 by linarith [eq4], show z = -y by linarith [eq3]] at h2 
      nlinarith 
    have eq9 : y = 3 ∨ y = -3 := by 
      have h11 : y^2 = 9 := eq8 
      have h12 : y^2 = 3^2 := by nlinarith 
      have h13 : y = 3 ∨ y = -3 := by 
        have h4 : y^2 = 9 := eq8 
        have h5 : y^2 - 9 = 0 := by linarith 
        have h6 : (y - 3) * (y + 3) = 0 := by 
          linarith 
        cases' (mul_eq_zero.mp h6) with h7 h8 
        · left 
          linarith 
        · right 
          linarith 
      tauto 
    cases' eq9 with h17 h17
    · 
      have hy10 : y = 3 := h17 
      have h11 : z = -3 := by linarith [eq3, hy10] 
      simp [eq4, hy10, h11] 
    · 
      have hy10 : y = -3 := h17 
      have h11 : z = 3 := by linarith [eq3, hy10] 
      simp [eq4, hy10, h11]