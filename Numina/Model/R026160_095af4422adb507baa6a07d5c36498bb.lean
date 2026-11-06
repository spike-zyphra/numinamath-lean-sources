import Mathlib

theorem algebra_236499 {f g : ℝ → ℝ} (hf : ∃ a b, f = fun x => x^2 + a * x + b)
    (hg : ∃ c d, g = fun x => x^2 + c * x + d) (h1 : g 6 = 35) (h2 : f (-1) / g (-1) = 21 / 20)
    (h3 : f 1 / g 1 = 21 / 20) : f 6 = 35 := by
  rcases hf with ⟨a, b, hf⟩
  rcases hg with ⟨c, d, hg⟩
  have eq1 : g 6 = 35 := h1
  simp [hg] at eq1
  have eqg : 6 * c + d = -1 := by
    nlinarith
  have hg1_ne_zero : g (-1) ≠ 0 := by
    by_contra h
    have eq2_at : f (-1) / g (-1) = 0 := by
      rw [h]
      norm_num [hf, hg]
    linarith [h2, eq2_at]
  have hg2_ne_zero : g 1 ≠ 0 := by
    by_contra h
    have eq3_at : f 1 / g 1 = 0 := by
      rw [h]
      norm_num [hf, hg]
    linarith [h3, eq3_at]
  have eq2 : 20 * (f (-1)) = 21 * (g (-1)) := by
    have h_eq2 : f (-1) / g (-1) = 21 / 20 := h2
    have hg1_ne_zero' : g (-1) ≠ 0 := hg1_ne_zero
    have h8 : 20 * (f (-1)) = 21 * (g (-1)) := by
      field_simp [hg1_ne_zero'] at h_eq2 ⊢ 
      <;> nlinarith
    linarith
  have eq5 : 20 * (f 1) = 21 * (g 1) := by
    have h_eq3 : f 1 / g 1 = 21 / 20 := h3
    have hg2_ne_zero' : g 1 ≠ 0 := hg2_ne_zero
    have h9 : 20 * (f 1) = 21 * (g 1) := by
      field_simp [hg2_ne_zero'] at h_eq3 ⊢
      <;> nlinarith
    linarith
  have eq6 : f 6 = 35 := by
    have eq7 : f 6 = 36 + 6 * a + b := by
      simp [hf]
      <;> ring
    have eq8 : 36 + 6 * a + b = 35 := by
      simp [hf, hg] at eq2 eq5
      ring_nf at eq2 eq5 eqg ⊢
      nlinarith [eqg]
    linarith [eq7, eq8]
  exact eq6