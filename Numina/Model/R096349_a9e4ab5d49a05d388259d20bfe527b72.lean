import Mathlib

theorem algebra_11375 {α β : ℂ} (h₁ : ∃ r : ℝ, r > 0 ∧ α + β = r) (h₂ : ∃ r : ℝ, r > 0 ∧ Complex.I * (α - 2 * β) = r)
    (h₃ : β = 3 + 2 * Complex.I) : α = 6 - 2 * Complex.I := by
  rcases h₁ with ⟨r₁, hr₁_pos, h₁_eq⟩
  rcases h₂ with ⟨r₂, hr₂_pos, h₂_eq⟩
  rw [h₃] at h₁_eq h₂_eq
  have eq1 := congr_arg Complex.re h₁_eq
  have eq2 := congr_arg Complex.im h₁_eq
  have eq3 := congr_arg Complex.re h₂_eq
  have eq4 := congr_arg Complex.im h₂_eq
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im] at eq1 eq2 eq3 eq4
  have h1 : α.im = -2 := by
    nlinarith
  have h2 : α.re = 6 := by
    nlinarith
  rw [Complex.ext_iff]
  simp [h1, h2]
  all_goals norm_num