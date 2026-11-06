import Mathlib

theorem algebra_21143 {z : ℂ} (hz : z.im = 164) (n : ℕ) (hn : n > 0) (h : z / (z + n) = 4 * .I) :
    n = 697 := by 
  have h1 : z ≠ 0 := by
    by_contra hz0
    rw [hz0] at h
    field_simp [Complex.ext_iff, mul_add, pow_two] at h ⊢
    <;> norm_num [Complex.ext_iff, mul_add, pow_two] at h ⊢ <;> try { tauto }
    <;> try { linarith }
    <;> try { ring_nf at h ⊢; linarith }
  have h2 : z + n ≠ 0 := by
    by_contra h3
    rw [h3] at h
    field_simp [Complex.ext_iff, mul_add, pow_two, h1] at h ⊢
    <;> norm_num [Complex.ext_iff, mul_add, pow_two, h1] at h ⊢
    <;> try { linarith }
    <;> try { ring_nf at h ⊢; linarith }
  have h3 : z = 4 * Complex.I * (z + n) := by 
    field_simp [h2] at h
    simpa using h
  simp [Complex.ext_iff] at h3 
  obtain ⟨zre, zim⟩ := z
  have hz_im : zim = 164 := hz
  norm_num [Complex.ext_iff] at h3
  have h_eq1 := h3.1
  have h_eq2 := h3.2
  have hn_eq : (n : ℝ) = (697 : ℝ) := by 
    nlinarith [h_eq1, h_eq2, hz_im]
  have h_n : n = 697 := by 
    exact_mod_cast hn_eq 
  exact h_n