import Mathlib

theorem algebra_163528 {a b c : ℂ} (h₀ : a^2 + a * b + b^2 = 1 + .I) (h₁ : b^2 + b * c + c^2 = -2)
    (h₂ : c^2 + c * a + a^2 = 1) :
    (a * b + b * c + c * a)^2 = (-11 - 4 * .I) / 3 := by
  simp [pow_two, Complex.ext_iff] at h₀ h₁ h₂ ⊢
  ring_nf at h₀ h₁ h₂ ⊢
  constructor
  · -- Real part
    nlinarith
  · -- Imaginary part
    nlinarith