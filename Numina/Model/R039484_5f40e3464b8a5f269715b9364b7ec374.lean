import Mathlib

theorem algebra_17014 :
  { (x^5 + y^5 + z^5) / (x*y*z*(x*y + x*z + y*z)) | (x : ℝ) (y : ℝ) (z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hsum : x + y + z = 0) (hprod : x * y + x * z + y * z ≠ 0) } = {-5} := by 
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, show that any element in the set is equal to -5
    rintro ⟨x, y, z, hx, hy, hz, hsum, hprod, ha⟩ 
    have h1 : x + y + z = 0 := hsum
    have h2 : z = -x - y := by linarith 
    have h3 : x^5 + y^5 + z^5 = -5 * (x * y * z) * (x * y + x * z + y * z) := by 
      rw [show z = -x - y by linarith] 
      ring
    have h4 : (x^5 + y^5 + z^5) / (x * y * z * (x * y + x * z + y * z)) = -5 := by
      have h5 : x * y * z * (x * y + x * z + y * z) ≠ 0 := by 
        apply mul_ne_zero 
        · -- Show that xyz ≠ 0
          apply mul_ne_zero 
          apply mul_ne_zero 
          exact hx
          exact hy
          exact hz
        · -- Show that (xy + xz + yz) ≠ 0
          exact hprod
      field_simp [h5] 
      <;> nlinarith 
    rw [h4] at ha 
    linarith 
  · -- Show that -5 is achievable 
    intro ha 
    rw [ha] 
    use 1, 1, -2 
    norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num 
    <;> norm_num