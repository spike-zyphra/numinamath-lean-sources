import Mathlib

theorem algebra_21459 {a b : ℂ} (h₀ : a * b = 21 - 20 * .I) (h₁ : Complex.abs b = 29) :
    Complex.abs a = 1 := by
  have h2 : Complex.abs (a * b) = Complex.abs (21 - 20 * Complex.I) := by 
    rw [h₀]
  have h3 : Complex.abs (a * b) = Complex.abs a * Complex.abs b := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h4 : Complex.abs (21 - 20 * Complex.I) = 29 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
  rw [h3] at h2
  rw [h4] at h2
  rw [h₁] at h2
  have h5 : Complex.abs a = 1 := by
    nlinarith
  exact h5