import Mathlib

theorem calculus_22257
    (u v c: EuclideanSpace ℝ (Fin 2)) (a b : ℝ) (h₀ : v = ![a, b]) (h₁ : u = ![√3, 1])
    (h₂ : a = 2 + b * √3) (h₃ : (orthogonalProjection (ℝ ∙ u) v) = c)(h₄ : ‖c‖ = √3) :
    a = 2 ∨ a = -1:= by
  rw [orthogonalProjection_singleton] at h₃
  rw [h₀] at h₃
  rw [h₁] at h₃
  simp at h₃
  rw[← real_inner_self_eq_norm_sq] at h₃
  norm_num at h₃
  rw [← h₃] at h₄
  rw [norm_smul] at h₄
  norm_num at h₄
  rw [norm_eq_sqrt_real_inner] at h₄
  norm_num at h₄
  have hsqrt4: √4 = 2  := by
    rw [show (4 : ℝ) = 2 ^ 2 by ring_nf]
    rw [Real.sqrt_sq_eq_abs]
    simp
  rw [hsqrt4] at h₄
  rw [h₂] at h₄
  ring_nf at h₄
  simp at h₄
  ring_nf at h₄
  apply_fun (. * 2) at h₄
  ring_nf at h₄
  have hl2 : 0 ≤ √3 * 2 := by simp
  rw [abs_eq hl2] at h₄
  obtain h₄ | h₄ := h₄
  . apply_fun fun n => (n - √3 * 2) / 4 at h₄
    ring_nf at h₄
    rw [h₄] at h₂
    ring_nf at h₂
    left
    exact h₂
  . apply_fun fun n => (n - √3 * 2) / 4 at h₄
    ring_nf at h₄
    rw [h₄] at h₂
    ring_nf at h₂
    rw [Real.sq_sqrt] at h₂
    ring_nf at h₂
    right
    exact h₂
    simp
