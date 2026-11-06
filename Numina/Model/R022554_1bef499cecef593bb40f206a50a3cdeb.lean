import Mathlib

theorem algebra_12881 {ω : ℂ} (hω : ω = -1 + Real.sqrt 2 * .I) :
    ((ω / (ω + 2)) ^ 20) * ((ω + 1 + 1 / ω) ^ 20) = 1 := by
  have h1 : ω = -1 + Real.sqrt 2 * Complex.I := hω
  have h2 : ω + 2 = 1 + Real.sqrt 2 * Complex.I := by
    rw [hω]
    ring
  have eq1 : ω / (ω + 2) = (1 + 2 * Real.sqrt 2 * Complex.I) / 3 := by
    rw [h2, hω]
    field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, add_mul]
    <;> ring_nf <;> norm_num
  have eq2 : ω + 1 + 1 / ω = (-1 + 2 * Real.sqrt 2 * Complex.I) / 3 := by
    rw [hω]
    field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, add_mul]
    <;> ring_nf <;> norm_num
  have eq3 : (ω / (ω + 2)) * (ω + 1 + 1 / ω) = -1 := by
    rw [eq1, eq2]
    field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, add_mul]
    <;> ring_nf <;> norm_num
  calc
    ((ω / (ω + 2)) ^ 20) * ((ω + 1 + 1 / ω) ^ 20)
        = ((ω / (ω + 2) ) * (ω + 1 + 1 / ω)) ^ 20 := by
          rw [mul_pow]
    _ = (-1) ^ 20 := by
        rw [eq3]
    _ = 1 := by
        norm_num