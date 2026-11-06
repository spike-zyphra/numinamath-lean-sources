import Mathlib

theorem algebra_259341 {z : ℂ} (hz : (2017 * z - 25) / (z - 2017) = 3 + 4 * .I) :
    Complex.abs z = 5 := by
  have h1 : z - 2017 ≠ 0 := by
    by_contra h
    have h2 : z = 2017 := by
      have h3 : z - 2017 = 0 := by
        simpa using h
      have : z = 2017 := by
        calc
          z = (z - 2017) + 2017 := by ring
          _ = 0 + 2017 := by rw [h3]
          _ = 2017 := by ring
      assumption
    rw [h2] at hz
    field_simp [Complex.ext_iff] at hz
    all_goals norm_num [Complex.ext_iff] at hz
  have h2 : 2017 * z - 25 = (3 + 4 * Complex.I) * (z - 2017) := by
    have h1' : z - 2017 ≠ 0 := h1
    field_simp [h1'] at hz ⊢
    <;> simpa using hz
  have h5 : z = (-6026 - 8068 * Complex.I) / (2014 - 4 * Complex.I) := by
    field_simp [h1, Complex.ext_iff] at h2 ⊢
    <;> ring_nf at h2 ⊢
    <;> norm_num [Complex.ext_iff] at h2 ⊢
    <;> constructor <;> nlinarith
  rw [h5]
  simp [Complex.abs, Complex.normSq, Complex.div_re, Complex.div_im, Complex.normSq]
  field_simp
  <;> norm_num [Real.sqrt_eq_iff_sq_eq]
  <;> ring_nf
  <;> norm_num