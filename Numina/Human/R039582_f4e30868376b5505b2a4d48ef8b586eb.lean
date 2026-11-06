import Mathlib

open Real

/- PROBLEM: Corners are sliced off a unit cube so that the six faces each become regular octagons. 
   What is the total volume of the removed tetrahedra? -/

theorem geometry_98147 (x : ℝ) (hx : x = (1 - 1 / sqrt 2)) : 
  8 * (x^3 / 6) = (10 - 7 * sqrt 2) / 3 := by 
{
  -- Insert the value of x, given by the remaining length of the edges of the cube.
  -- Then simplify.
  rw [hx]
  field_simp
  ring_nf
  norm_num

  -- Evaluate the powers of √2 and conclude by rearranging.
  have hsq23 : (sqrt 2)^3 = 2 * sqrt 2 := by 
  {
    rw [pow_succ]
    simp
  }
  rw [hsq23]

  have : (sqrt 2)^4 = 4 := by 
  {
    rw [pow_succ, hsq23, mul_assoc, ←Real.sqrt_mul, Real.sqrt_mul_self]
    norm_num
    norm_num
    norm_num
  }
  rw [this]
  ring
}