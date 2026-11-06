import Mathlib

theorem algebra_328021 {x y z : ℝ} (h1 : x * y * z = 1) (h2 : x + y + z = 2) (h3 : x ^ 2 + y ^ 2 + z ^ 2 = 16) :
    1 / (x * y + 2 * z) + 1 / (y * z + 2 * x) + 1 / (z * x + 2 * y) = -4 / 13 := by
  have h4 : x * y + y * z + z * x = -6 := by
    have eq1 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
      ring
    rw [h2] at eq1
    linarith [h3, eq1]
  have eq1 : (x * y + 2 * z) ≠ 0 := by
    by_contra h
    have h5 : x * y = -2 * z := by linarith
    have h6 : x * y * z = -2 * z^2 := by 
      have h7 : x * y = -2 * z := by linarith
      have h8 : x * y * z = (-2 * z) * z := by
        have eqc : x * y = -2 * z := by linarith
        calc 
          x * y * z = (x * y) * z := by ring
          _ = (-2 * z) * z := by 
            rw [eqc]
      linarith
    -- Now we have h6 : x * y * z = -2 * z^2
    have eq2 : (x * y * z) = 1 := h1
    rw [h6] at eq2
    have eq3 : -2 * z ^ 2 = 1 := by linarith
    have eq4 : z ^ 2 < 0 := by 
      nlinarith
    have eq5 : z ^ 2 ≥ 0 := sq_nonneg z
    nlinarith
  have eq2 : (y * z + 2 * x) ≠ 0 := by
    by_contra h
    have h5 : y * z = -2 * x := by linarith
    have eq3 : x * y * z = -2 * x^2 := by
      have h7 : y * z = -2 * x := by linarith
      calc
        x * y * z = x * (y * z) := by ring
        _ = x * (-2 * x) := by rw [h7]
        _ = -2 * x^2 := by ring
    have eq4 : (x * y * z) = 1 := h1
    rw [eq3] at eq4
    have eq5 : -2 * x ^ 2 = 1 := by linarith
    have eq6 : x ^ 2 < 0 := by 
      nlinarith
    have eq7 : x ^ 2 ≥ 0 := sq_nonneg x
    nlinarith
  have eq3 : (z * x + 2 * y) ≠ 0 := by
    by_contra h
    have h5 : z * x = -2 * y := by linarith
    have eq3 : x * y * z = -2 * y^2 := by
      have h7 : z * x = -2 * y := by linarith
      calc 
        x * y * z = (z * x) * y := by ring
        _ = (-2 * y) * y := by 
          rw [h7]
        _ = -2 * y^2 := by ring
    have eq2 : (x * y * z) = 1 := h1
    rw [eq3] at eq2
    have eq3 : -2 * y ^ 2 = 1 := by linarith
    have eq4 : y ^ 2 < 0 := by 
      nlinarith
    have eq5 : y ^ 2 ≥ 0 := sq_nonneg y 
    nlinarith
  have h6 : (x * y + 2 * z) * (y * z + 2 * x) * (z * x + 2 * y) = 169 := by
    nlinarith [sq_nonneg (x * y * z - 1), sq_nonneg (x * y + y * z + z * x + 6), sq_nonneg (x + y + z - 2), 
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h8 : (x * y + 2 * z) * (y * z + 2 * x) + (x * y + 2 * z) * (z * x + 2 * y) + (y * z + 2 * x) * (z * x + 2 * y) = -52 := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
            sq_nonneg (x * y * z - 1)]
  field_simp [eq1, eq2, eq3]
  linarith [h8, h6]