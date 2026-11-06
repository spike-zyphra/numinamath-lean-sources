import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_248770 {f : ℝ → ℝ} (hf : f = λ x => x^3 + x)
  (h : ∀ θ ∈ Icc 0 (π/2), f (m * cos θ) + f (1 - m) > 0) :
  m < 1 := by
    have h1 := h (π / 2) (by 
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    )
    have h_cos : cos (π / 2) = 0 := Real.cos_pi_div_two
    rw [h_cos] at h1
    simp [hf] at h1
    nlinarith [sq_nonneg (m - 1), sq_nonneg (1 - m - 1), Real.pi_pos]