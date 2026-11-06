import Mathlib

open Real Set
open scoped Real

theorem calculus_202447 (f : ℝ → ℝ) (hf : f = λ x => 1 / cos x - tan x)
  (x : ℝ) (hx : x ∈ Ico 0 (π/2)) :
  f x ≤ 1 ∧ ∃ x ∈ Ico 0 (π/2), f x = 1 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : f x = (1 - sin x) / cos x := by 
    rw [hf]
    have h2 : tan x = (sin x) / (cos x) := by 
      rw [tan_eq_sin_div_cos]
    simp only [h2]
    have hcos_pos : cos x > 0 := cos_pos_of_mem_Ioo (show x ∈ Ioo (-(π / 2)) (π / 2) by
      constructor <;> linarith [Real.pi_pos, hx1, hx2]
    )
    field_simp [hcos_pos]
    <;> ring
  constructor
  · -- Show f x ≤ 1
    rw [h1]
    have hcos : cos x > 0 := cos_pos_of_mem_Ioo (show x ∈ Ioo (-(π / 2)) (π / 2) by
      constructor <;> linarith [Real.pi_pos, hx1, hx2]
    )
    have h2 : (1 - sin x) / cos x ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hcos).mpr
      have h5 : 1 - sin x ≤ (cos x : ℝ) := by
        nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ x by linarith) (show x ≤ Real.pi by linarith [Real.pi_pos, hx2]), sq_nonneg (sin x - 0), sq_nonneg (cos x - 1), sq_nonneg (x - 0)]
      nlinarith
    linarith
  · -- Show ∃ x ∈ Ico 0 (π / 2), f x = 1
    use (0)
    constructor
    · -- Show 0 ∈ Ico 0 (π / 2)
      constructor <;> linarith [Real.pi_pos]
    · -- Show f 0 = 1
      have h2 : f 0 = 1 := by
        rw [hf]
        have hcos0 : cos (0 : ℝ) = 1 := by 
          exact cos_zero
        have htan0 : tan (0 : ℝ) = 0 := by
          rw [tan_eq_sin_div_cos]
          simp [sin_zero, cos_zero]
        simp_all [hcos0, htan0]
      exact h2