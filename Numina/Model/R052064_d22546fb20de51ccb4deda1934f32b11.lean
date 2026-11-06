import Mathlib

theorem algebra_303666 (x y z : ℝ) (h₀ : 13*x+5*y+9*z=9.25) (h₁ : 2*x+4*y+3*z=3.20) :
    x+y+z=1.05 := by
  have h2 : y = x + (0.05 : ℝ) := by
    have h3 : -7 * x + 7 * y = (0.35 : ℝ) := by
      ring_nf at h₀ h₁ ⊢
      linarith [h₀, h₁]
    have h4 : y = x + (0.05 : ℝ) := by
      ring_nf at h3 ⊢
      linarith
    linarith [h4]

  have h4 : z = 1.00 - 2 * x := by
    rw [show y = x + (0.05 : ℝ) by linarith [h2]] at h₁
    ring_nf at h₁ ⊢
    linarith

  have h5 : x + y + z = (1.05 : ℝ) := by
    rw [show y = x + (0.05 : ℝ) by linarith [h2], show z = (1.00 : ℝ) - 2 * x by linarith [h4]]
    ring_nf

  linarith [h5]