import Mathlib


theorem algebra_93161 {α γ : ℂ} (f : ℂ → ℂ) (hf : ∀ z, f z = (4 + Complex.I) * z ^ 2 + α * z + γ)
    (h₁ : ∃ r : ℝ, f 1 = r) (h₂ : ∃ r : ℝ, f Complex.I = r) :
    Complex.abs α + Complex.abs γ ≥ Real.sqrt 2 := by
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩
  have eq1 : f 1 = (4 + Complex.I) * (1:ℂ) ^ 2 + α * (1:ℂ) + γ := hf 1
  rw [eq1] at hr₁
  have eq2 : f Complex.I = (4 + Complex.I) * (Complex.I:ℂ) ^ 2 + α * (Complex.I:ℂ) + γ := hf Complex.I
  rw [eq2] at hr₂

  have h_eq1 : (4 + Complex.I) * (1:ℂ) ^ 2 + α * (1:ℂ) + γ = r₁ := by
    simpa using hr₁

  have h_eq2 : (4 + Complex.I) * (Complex.I:ℂ) ^ 2 + α * (Complex.I:ℂ) + γ = r₂ := by
    simpa using hr₂

  have eq1 := congr_arg Complex.im h_eq1
  have eq2 := congr_arg Complex.im h_eq2
  have eq3 := congr_arg Complex.re h_eq1
  have eq4 := congr_arg Complex.re h_eq2
  simp [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re] at eq1 eq2 eq3 eq4
  have h1 : Complex.abs α = Real.sqrt (α.re ^ 2 + α.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have h2 : Complex.abs γ = Real.sqrt (γ.re ^ 2 + γ.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h1, h2]

  have h7 : α.im = α.re - 2 := by
    nlinarith
  have h12 : Complex.abs α = Real.sqrt (2 * α.re ^ 2 - 4 * α.re + 4) := by
    rw [h1]
    have : α.im = α.re - 2 := h7
    rw [this]
    ring_nf
  have h3 : Complex.abs α ≥ Real.sqrt 2 := by
    have h4 : Complex.abs α = Real.sqrt (2 * α.re ^ 2 - 4 * α.re + 4) := h12
    rw [h4]
    have h5 : Real.sqrt (2 * α.re ^ 2 - 4 * α.re + 4) ≥ Real.sqrt 2 := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (α.re - 1)]
    linarith
  have h4 : Complex.abs γ ≥ 0 := by
    apply Real.sqrt_nonneg
  linarith [h3, h4]