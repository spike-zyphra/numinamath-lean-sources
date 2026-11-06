import Mathlib

open Real Set
open scoped Real

theorem algebra_321535 (f : ℝ → ℝ)
  (h₀ : ∀ x ∈ Ioo 0 (π/2), f x = 1 / sin x ^ 2 + 12 * sqrt 3 / cos x) :
  IsLeast {y | ∃ x ∈ Ioo 0 (π/2), f x = y} 28 := by

  constructor
  · -- Show that 28 is in the set
    use Real.pi / 6
    constructor
    · -- Show that π/6 is in the open interval (0, π/2)
      have h1 : 0 < Real.pi / 6 := by
        linarith [Real.pi_pos]
      have h2 : Real.pi / 6 < Real.pi / 2 := by
        linarith [Real.pi_pos]
      exact ⟨h1, h2⟩
    · -- Show that f(π/6) = 28
      have h4 : f (Real.pi / 6) = 28 := by
        have h5 : f (Real.pi / 6) = 1 / sin (Real.pi / 6) ^ 2 + 12 * Real.sqrt 3 / cos (Real.pi / 6) := h₀ (Real.pi / 6) (by
          constructor
          · -- Show that 0 < Real.pi / 6
            linarith [Real.pi_pos]
          · -- Show that Real.pi / 6 < Real.pi / 2
            linarith [Real.pi_pos]
        )
        rw [h5]
        have h6 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
        have h7 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
        rw [h6, h7]
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith [h4]
  · -- Show that 28 is the minimum
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : 0 < x := hx.1
    have hx2 : x < Real.pi / 2 := hx.2
    have h8 : f x = 1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x := h₀ x (by
      exact hx
    )
    rw [h8] at hfx
    have h9 : 0 < sin x := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, hx1, hx2]
    have h10 : 0 < cos x := by
      have : x < Real.pi / 2 := hx2
      have h11 : cos x > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith
      linarith
    have h11 : 1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x ≥ 28 := by
      have h15 : 0 < sin x ^ 2 * cos x := by
        positivity
      have h16 : (1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x - 28) = (cos x + 12 * Real.sqrt 3 * sin x ^ 2 - 28 * sin x ^ 2 * cos x) / (sin x ^ 2 * cos x) := by
        field_simp [h9.ne', h10.ne']
        <;> ring
      have h17 : cos x + 12 * Real.sqrt 3 * sin x ^ 2 - 28 * sin x ^ 2 * cos x ≥ 0 := by
        nlinarith [sq_nonneg (cos x - Real.sqrt 3 / 2), sq_nonneg (sin x ^ 2 - 1 / 4), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sin x * Real.sqrt 3), Real.sin_sq_add_cos_sq x, mul_pos h9 h10, sq_nonneg (cos x - 1), sq_nonneg (sin x - 1 / 2), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 ^ 2)]
      have h18 : (cos x + 12 * Real.sqrt 3 * sin x ^ 2 - 28 * sin x ^ 2 * cos x) / (sin x ^ 2 * cos x) ≥ 0 := by
        apply div_nonneg
        linarith
        linarith
      nlinarith
    linarith