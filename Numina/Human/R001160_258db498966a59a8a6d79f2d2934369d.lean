import Mathlib

/- If $z^2 + z + 1 = 0,$ find
\[z^{49} + z^{50} + z^{51} + z^{52} + z^{53}.\] -/
theorem algebra_20787 {z : ℂ} (hz : z^2 + z + 1 = 0) :
    z^49 + z^50 + z^51 + z^52 + z^53 = -1 := by
  -- from z^2+z+1, we have z^3=1. because z^3-1 = (z-1)(z^2+z+1)
  have h1: z^3 = 1 := by
    have: z^3-1 = 0 := by
      have: z^3-1 = (z-1)*(z^2+z+1) := by ring
      rw [this, hz]; simp
    rw [← add_zero 1, ← this]; ring
  -- and z^48 = (z^3)^16 z^51 = (z^3)^17, thus we can simplify
  have h2: z^49 = z := by
    have: z^49 = z*((z^3)^16) := by ring
    rw [this, h1]; simp
  have h3: z^50 = z^2 := by
    rw [pow_succ, h2]; ring
  have h4: z^51 = 1 := by
    have: z^51 = (z^3)^17 := by ring
    rw [this, h1]; simp
  have h5: z^52 = z := by
    rw [pow_succ, h4]; simp
  have h6: z^53 = z^2 := by
    rw [pow_succ, h5]; ring
  -- it simplifies to 2z^2+2z+1, = 2(z^2+z+1) - 1 = -1.
  have h7: z^49 + z^50 + z^51 + z^52 + z^53 = 2*(z^2+z+1)-1 := by
    rw [h2,h3,h4,h5,h6]; ring
  rw [h7, hz]; simp