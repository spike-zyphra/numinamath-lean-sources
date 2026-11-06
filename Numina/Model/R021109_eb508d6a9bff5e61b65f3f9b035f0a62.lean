import Mathlib

theorem algebra_165654 {x y z : ℂ} (h₀ : x * y * z = -4) (h₁ : (x + 1) * (y + 1) * (z + 1) = 7)
    (h₂ : (x + 2) * (y + 2) * (z + 2) = -3) :
    (x + 3) * (y + 3) * (z + 3) = -28 := by
  have eq1 : x * y + y * z + z * x = 47 / 2 := by
    have eq2 : (x + 1) * (y + 1) * (z + 1) = x * y * z + (x * y + y * z + z * x) + (x + y + z) + 1 := by
      ring
    rw [h₀] at eq2
    rw [h₁] at eq2
    have eq3 : (x * y + y * z + z * x : ℂ) + (x + y + z : ℂ) = 10 := by
      simp [Complex.ext_iff] at eq2 ⊢
      constructor
      · linarith
      · linarith
    have eq4 : (x + 2) * (y + 2) * (z + 2) = x * y * z + 2 * (x * y + y * z + z * x) + 4 * (x + y + z) + 8 := by
      ring
    rw [h₀] at eq4
    rw [h₂] at eq4
    have eq6 : 2 * (x * y + y * z + z * x : ℂ) + 4 * (x + y + z : ℂ) = -7 := by
      simp [Complex.ext_iff] at eq4 ⊢
      constructor
      · linarith
      · linarith
    have eq7 : (x * y + y * z + z * x : ℂ) = 47 / 2 := by
      have h1 : (x * y + y * z + z * x : ℂ) + (x + y + z : ℂ) = 10 := by
        exact_mod_cast eq3
      have h2 : 2 * (x * y + y * z + z * x : ℂ) + 4 * (x + y + z : ℂ) = -7 := by
        exact_mod_cast eq6
      simp [Complex.ext_iff] at h1 h2 ⊢
      constructor
      · 
        ring_nf at h1 h2 ⊢ 
        linarith 
      · 
        ring_nf at h1 h2 ⊢ 
        linarith 
    exact_mod_cast eq7
  have eq7 : x + y + z = -27 / 2 := by
    have eq2 : (x + 1) * (y + 1) * (z + 1) = x * y * z + (x * y + y * z + z * x) + (x + y + z) + 1 := by
      ring
    rw [h₀] at eq2
    rw [h₁] at eq2
    have eq3 : (x * y + y * z + z * x : ℂ) + (x + y + z : ℂ) = 10 := by
      simp [Complex.ext_iff] at eq2 ⊢
      constructor
      · linarith
      · linarith
    have eq4 : (x + 2) * (y + 2) * (z + 2) = x * y * z + 2 * (x * y + y * z + z * x) + 4 * (x + y + z) + 8 := by
      ring
    rw [h₀] at eq4
    rw [h₂] at eq4
    have eq6 : 2 * (x * y + y * z + z * x : ℂ) + 4 * (x + y + z : ℂ) = -7 := by
      simp [Complex.ext_iff] at eq4 ⊢
      constructor
      · linarith
      · linarith
    have eq8 : (x + y + z : ℂ) = -27 / 2 := by
      have h1 : (x * y + y * z + z * x : ℂ) + (x + y + z : ℂ) = 10 := by
        exact_mod_cast eq3
      have h2 : 2 * (x * y + y * z + z * x : ℂ) + 4 * (x + y + z : ℂ) = -7 := by
        exact_mod_cast eq6
      simp [Complex.ext_iff] at h1 h2 ⊢
      constructor
      · 
        ring_nf at h1 h2 ⊢ 
        linarith 
      · 
        ring_nf at h1 h2 ⊢ 
        linarith 
    exact_mod_cast eq8
  have eq8 : (x + 3) * (y + 3) * (z + 3) = x * y * z + 3 * (x * y + y * z + z * x) + 9 * (x + y + z) + 27 := by
    ring
  rw [eq8]
  rw [h₀, eq1, eq7]
  field_simp [Complex.ext_iff]
  <;> norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  <;> norm_num