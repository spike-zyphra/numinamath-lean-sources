import Mathlib
open InnerProductSpace
theorem calculus_23032 (t u: EuclideanSpace ℝ (Fin 3)) (a : ℝ) (h₀ : t = ![2,a,4]) (h₁ : u = ![-1,4,2])

    (h₂ : ⟪t, u⟫_ℝ = 0) :
    a = -3 / 2 := by 
  rw [h₀, h₁] at h₂
  simp [Finset.sum] at h₂ 
  linarith