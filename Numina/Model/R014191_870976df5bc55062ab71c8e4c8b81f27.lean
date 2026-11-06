import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194346 {f : ℝ → ℝ}
  (hf : f = λ x => (1 + sin x - cos x) / (1 + sin x + cos x)) :
  ∀ x ∈ Ioo (-π/2) (π/2), f (-x) = -f x := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin (-x) = -sin x := by
    rw [sin_neg]
  have h2 : cos (-x) = cos x := by
    rw [cos_neg]
  have h3 : f (-x) = (1 + sin (-x) - cos (-x)) / (1 + sin (-x) + cos (-x)) := by
    rw [hf]
  have h4 : f x = (1 + sin x - cos x) / (1 + sin x + cos x) := by
    rw [hf]
  rw [h3] at *
  rw [h4] at *
  rw [h1, h2]
  have h5 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · nlinarith [pi_pos, hx1, hx2]
    · nlinarith [pi_pos, hx1, hx2]
  have h7 : 1 + sin x + cos x ≠ 0 := by
    have h1 : 1 + sin x + cos x > 0 := by
      nlinarith [sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x), sq_pos_of_pos h5]
    linarith
  have h8 : 1 + -sin x + cos x ≠ 0 := by
    have h1 : 1 + -sin x + cos x > 0 := by
      nlinarith [sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x), sq_pos_of_pos h5]
    linarith
  field_simp [h7, h8]
  <;> ring_nf <;> simp [sin_sq, cos_sq] <;> nlinarith [sin_sq_add_cos_sq x]