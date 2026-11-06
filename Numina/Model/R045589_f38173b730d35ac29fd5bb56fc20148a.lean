import Mathlib

open Real Set

theorem algebra_20603 (f : ℝ → ℝ) (hf : f = fun t => t / sqrt (t - 3)) :
    IsLeast {x | ∃ t, t > 3 ∧ f t = x} (2 * sqrt 3) := by
  constructor
  · -- Show that $2 \sqrt{3}$ is in the set.
    use 6
    constructor
    · norm_num
    · -- Show that f 6 = 2 * sqrt 3
      rw [hf]
      have h1 : sqrt (6 - 3 : ℝ) = Real.sqrt 3 := by
        norm_num
      simp [h1]
      have h2 : (6 : ℝ) / Real.sqrt 3 = 2 * Real.sqrt 3 := by
        field_simp [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith [h2]
  · -- Show that $2 \sqrt{3}$ is minimal in the set.
    intro x hx
    rcases hx with ⟨t, ht, hfx⟩
    rw [hf] at hfx
    have ht' : t > 3 := ht
    have ht1 : t - 3 > 0 := by linarith
    have h2 : sqrt (t - 3) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h3 : sqrt (t - 3) ^ 2 = t - 3 := by
      rw [Real.sq_sqrt]
      linarith
    have eq1 : (fun (t : ℝ) => t / sqrt (t - 3)) t = t / sqrt (t - 3) := by rfl
    have eq2 : t / sqrt (t - 3) ≥ 2 * sqrt 3 := by
      have h4 : sqrt (t - 3) > 0 := h2
      have h5 : sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      have h6 : t / sqrt (t - 3) ≥ 2 * sqrt 3 := by
        have h7 : sqrt 3 > 0 := h5
        have h8 : sqrt (t - 3) > 0 := h2
        have h9 : t / sqrt (t - 3) - 2 * sqrt 3 ≥ 0 := by
          have h10 : t - 2 * sqrt 3 * sqrt (t - 3) ≥ 0 := by
            nlinarith [sq_nonneg (t - 6), sq_nonneg (sqrt (t - 3) - sqrt 3), 
              Real.sqrt_nonneg (t - 3), Real.sqrt_nonneg 3, 
              Real.sq_sqrt (show 0 ≤ (t - 3 : ℝ) by linarith), 
              Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
              mul_nonneg (Real.sqrt_nonneg (t - 3)) (Real.sqrt_nonneg 3)
            ]
          have h11 : t / sqrt (t - 3) - 2 * sqrt 3 = (t - 2 * sqrt 3 * sqrt (t - 3)) / sqrt (t - 3) := by
            field_simp [h2]
            <;> nlinarith
          rw [h11]
          apply div_nonneg
          linarith
          all_goals positivity
        linarith
      linarith
    simp at hfx
    linarith [hfx, eq2]