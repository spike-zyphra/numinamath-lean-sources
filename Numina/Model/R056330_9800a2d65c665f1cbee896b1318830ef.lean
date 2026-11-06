import Mathlib

theorem algebra_10264 {z : ℂ} (hz : z = (2 + 6 * .I) / (1 - .I)) :
    Complex.abs z = 2 * Real.sqrt 5 := by 
  rw [hz]
  have h1 : (2 + 6 * Complex.I) / (1 - Complex.I) = -2 + 4 * Complex.I := by
    field_simp [Complex.ext_iff, Complex.I_mul_I]
    norm_num
    <;> ring_nf <;> norm_num
  rw [h1]
  simp [Complex.abs, Complex.normSq]
  ring_nf
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> try { nlinarith }
  <;> try { tauto }
  <;> norm_num
  all_goals ring_nf <;> norm_num