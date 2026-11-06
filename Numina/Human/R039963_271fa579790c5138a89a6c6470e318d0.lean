import Mathlib
/-Solve for x, y, z ∈ ℝ+ the following system of equations
xy+yz+zx=12, xyz=2+x+y+z.-/
theorem algebra_132858 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y + y * z + z * x = 12) (h2 : x * y * z = 2 + x + y + z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
 -- we'll use completing the square approach on each equation
  have h3 : x + y + z ≥ 6 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

  have h4 : x * y * z ≤ 8 := by
    nlinarith [sq_nonneg (x * y - 4), sq_nonneg (y * z - 4), sq_nonneg (z * x - 4),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h1]

  have h5 : x * y * z = 8 := by
    nlinarith [h2, h3, h4]

  have h6 : x = y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h1, h5]

  have h7 : y = z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h1, h5]

  have h8 : z = x := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h1, h5]

  have h9 : x + y + z = 6 := by 
    nlinarith [h2, h5]

  have hx2 : x = 2 := by
    have h10 : x = y := h6
    have h11 : y = z := h7
    have h12 : z = x := h8
    have h13 : x + y + z = 6 := h9
    nlinarith [h10, h11, h13]

  have hy2 : y = 2 := by
    have h10 : x = y := h6
    have hx2 : x = 2 := hx2
    linarith

  have hz2 : z = 2 := by
    have h11 : y = z := h7
    have hy2 : y = 2 := hy2
    linarith

  exact ⟨hx2, hy2, hz2⟩