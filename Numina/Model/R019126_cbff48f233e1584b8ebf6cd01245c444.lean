import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11239 : IsGreatest {y | ∃ x : ℝ, y = (sin x - 1) * (cos x - 1) / (2 + sin (2 * x))} 1 := by
  constructor
  · -- We need to prove that 1 is in the set
    use -(Real.pi / 2)
    have h1 : sin (-(Real.pi / 2)) = -1 := by
      rw [sin_neg]
      simp [sin_pi_div_two]
    have h2 : cos (-(Real.pi / 2)) = 0 := by
      rw [cos_neg]
      simp [cos_pi_div_two]
    have h3 : sin (2 * (-(Real.pi / 2)) ) = 0 := by
      have h4 : 2 * (-(Real.pi / 2)) = -Real.pi := by ring
      rw [h4]
      simp [sin_neg, sin_pi]
    rw [h1, h2, h3]
    norm_num
  · -- We need to prove that 1 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h4 : (sin x - 1) * (cos x - 1) ≤ 2 + sin (2 * x) := by
      have h5 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      have h6 : sin (2 * x) = 2 * sin x * cos x := by
        rw [Real.sin_two_mul]
      rw [h6]
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x - 1), sq_nonneg (cos x - 1), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x, mul_nonneg (show (0 : ℝ) ≤ sin x ^ 2 by nlinarith) (show (0 : ℝ) ≤ cos x ^ 2 by nlinarith)]
    have h8 : 2 + sin (2 * x) > 0 := by
      have h7 : sin (2 * x) ≥ -1 := by
        have h8 : -1 ≤ sin (2 * x) ∧ sin (2 * x) ≤ 1 := by
          apply sin_mem_Icc
        linarith
      linarith
    have h9 : (sin x - 1) * (cos x - 1) / (2 + sin (2 * x)) ≤ 1 := by
      apply (div_le_iff₀ h8).mpr
      nlinarith
    have h10 : (sin x - 1) * (cos x - 1) / (2 + sin (2 * x)) ≤ 1 := h9
    linarith [h10, hx]