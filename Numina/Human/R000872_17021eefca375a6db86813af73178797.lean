import Mathlib

/- What is the perimeter, in units, of a rhombus if its area is 120 square units and one diagonal is 10 units? -/
theorem algebra_18756 (diagonala diagonalb side perimeter area : ℝ) (h1 : side = √((diagonala / 2) ^ 2 + (diagonalb / 2) ^ 2)) (h2 : perimeter = 4 * side) (h3 : area = 1 / 2 * diagonala * diagonalb) (h4 : diagonala = 10) (h5 : area = 120) : perimeter = 52 := by
  -- the other diagonal is $24$
  have h6 : diagonalb = 24 := by
    rw [h5, h4] at h3
    linarith
  rw [h2, h1, h4, h6]
  ring_nf
  have eq : (169 : ℝ) = 13 ^ 2 := by
    norm_num
  -- so the perimeter is $52$
  rw [eq, Real.sqrt_sq (by exact Nat.ofNat_nonneg' 13)]
  norm_num