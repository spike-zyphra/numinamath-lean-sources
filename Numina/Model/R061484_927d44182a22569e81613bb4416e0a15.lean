import Mathlib

theorem algebra_20612 {z : ℂ} (hz : 2 * z + Complex.I = Complex.I * z + 3) :
    z = 7 / 5 + 1 / 5 * Complex.I := by 
  have eq1 : 2 * z + Complex.I = Complex.I * z + 3 := hz
  have eq2 : z * (2 - Complex.I) = 3 - Complex.I := by
    calc
      z * (2 - Complex.I) = 2 * z - Complex.I * z := by ring
      _ = (2 * z + Complex.I) - Complex.I * z - Complex.I := by ring
      _ = (Complex.I * z + 3) - Complex.I * z - Complex.I := by rw [eq1]
      _ = 3 - Complex.I := by ring
  have eq3 : z = (3 - Complex.I) / (2 - Complex.I) := by
    rw [←eq2]
    field_simp [Complex.ext_iff, Complex.I_mul_I]
    <;> norm_num [Complex.ext_iff]
    <;> try { ring }
  rw [eq3]
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num [Complex.ext_iff]
  <;> try { ring }