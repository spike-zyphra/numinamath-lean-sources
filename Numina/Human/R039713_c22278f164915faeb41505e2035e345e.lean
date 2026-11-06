import Mathlib
open Real

theorem algebra_160062 (a : ℝ) (ha : a > 0) (x y : ℝ) :
    (∃ θ ∈ Set.Icc 0 π, (x, y) = (a * (θ - sin θ), a * (1 - cos θ))) ↔ (x = a * arccos (1 - y / a) - sqrt (2 * y * a - y ^ 2) ∧ 0 ≤ y ∧ y ≤ 2 * a) := by
  constructor
  . rintro ⟨θ, hθ, _, _⟩
    have h₀ := cos_mem_Icc θ
    simp at h₀
    refine ⟨?_, by nlinarith, by nlinarith⟩
    apply eq_sub_of_add_eq
    rw [add_comm]
    apply add_eq_of_eq_sub
    rw [<-sq_eq_sq₀ (by positivity), sq_sqrt (by nlinarith [show a * (1 - cos θ) ≥ 0 by nlinarith, show a * (1 - cos θ) ≤ 2 * a by nlinarith])]
    <;> rw [mul_div_cancel_left₀ _ ha.ne', sub_sub_cancel, arccos_cos hθ.1 hθ.2]
    . nlinarith [cos_sq_add_sin_sq θ, sq_nonneg a]
    . nlinarith [sin_nonneg_of_mem_Icc hθ]
  . rintro ⟨hxy, hy₀, hy₁⟩
    use arccos (1 - y / a)
    have h₀ : 0 ≤ y / a := by positivity
    have h₁ : y / a ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      exact hy₁
    simp [arccos_le_pi (1 - y / a), arccos_nonneg (1 - y / a)]
    refine ⟨?_, ?_⟩
    . rw [sin_arccos, mul_sub]
      nth_rw 3 [show a = sqrt (a ^ 2) by field_simp]
      rw [<-sqrt_mul (sq_nonneg a)]
      field_simp at hxy ⊢
      ring_nf at hxy ⊢
      exact hxy
    . rw [cos_arccos (show -1 ≤ 1 - y / a by linarith) (show 1 - y / a ≤ 1 by linarith)]
      field_simp

