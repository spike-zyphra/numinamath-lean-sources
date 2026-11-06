import Mathlib

open Real Set
open scoped Real

theorem algebra_134678 {x : ℝ} (hx : x ∈ Icc (-1) 1) (θ : ℝ)
  (hθ : θ = arcsin x) (hθ1 : θ ∈ Icc (-π/2) (-π/4)) :
  arcsin (2*x*sqrt (1 - x^2)) = -(π + 2*θ) := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hθ1 with ⟨h1, h2⟩
  have h3 : arcsin x = θ := by
    linarith [hθ]
  have h4 : 2 * x * sqrt (1 - x ^ 2) = sin (2 * θ) := by
    have hx11 : sin θ = x := by 
      rw [show θ = arcsin x by linarith [hθ]]
      simp [sin_arcsin, hx1, hx2]
    have hx12 : cos θ = Real.sqrt (1 - x^2) := by
      rw [show θ = arcsin x by linarith [hθ]]
      rw [cos_arcsin]
      all_goals
        nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith)]
    have h7 : sin (2 * θ) = 2 * sin θ * cos θ := by
      rw [sin_two_mul]
    rw [h7, hx11, hx12]
    <;> ring_nf <;> norm_num
  have h12 : arcsin (2 * x * sqrt (1 - x ^ 2)) = arcsin (sin (2 * θ)) := by 
    rw [h4]
  have h13 : arcsin (sin (2 * θ)) = -(π + 2 * θ) := by
    have h14 : sin (2 * θ) = -sin (π + 2 * θ) := by
      rw [sin_add, sin_pi, cos_pi]
      ring_nf
    have h15 : arcsin (sin (2 * θ)) = arcsin (-sin (π + 2 * θ)) := by
      rw [h14]
      <;> ring_nf
    have h16 : arcsin (-sin (π + 2 * θ)) = - arcsin (sin (π + 2 * θ)) := by
      rw [arcsin_neg]
      <;> ring_nf
    have h17 : arcsin (sin (π + 2 * θ)) = π + 2 * θ := by
      have h18 : -(π / 2) ≤ π + 2 * θ := by
        nlinarith [Real.pi_pos, h1, h2]
      have h19 : π + 2 * θ ≤ π / 2 := by
        nlinarith [Real.pi_pos, h1, h2]
      have h20 : arcsin (sin (π + 2 * θ)) = π + 2 * θ := by
        rw [Real.arcsin_sin]
        all_goals
          nlinarith [Real.pi_pos, h1, h2]
      linarith [h20]
    rw [h15, h16, h17]
    <;> ring_nf
  rw [h12, h13]