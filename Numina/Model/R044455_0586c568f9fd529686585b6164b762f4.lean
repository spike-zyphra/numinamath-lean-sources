import Mathlib

theorem algebra_108402 {f : ℝ → ℝ} (hf : ∀ x > 0, f x = f 1 * x + f 2 / x - 1) :
    IsLeast {y | ∃ x > 0, f x = y} (Real.sqrt 3 - 1) := by
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  have hf2 : f 2 = 1 := by
    norm_num at h1
    nlinarith 
  have hf1 : f 1 = 3 / 4 := by
    rw [hf2] at h2
    norm_num at h2
    nlinarith
  constructor
  · -- Show that Real.sqrt 3 - 1 is in the set.
    use 2 / Real.sqrt 3
    constructor
    · -- Show that 2 / Real.sqrt 3 > 0.
      positivity
    · -- Show f(2 / Real.sqrt 3) = Real.sqrt 3 - 1.
      have h3 := hf (2 / Real.sqrt 3) (by positivity)
      rw [h3]
      rw [hf1, hf2]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
  · -- Show that Real.sqrt 3 - 1 is the least element in the set.
    intro y hy
    rcases hy with ⟨x, hx, h4⟩
    have h5 := hf x hx
    rw [h5] at h4
    rw [hf1, hf2] at h4
    have h6 : (3 / 4) * x + 1 / x ≥ Real.sqrt 3 := by
      have h61 : x > 0 := hx
      have h62 : (3 / 4) * x + 1 / x - Real.sqrt 3 ≥ 0 := by
        have h63 : x > 0 := hx
        have h64 : (3 / 4) * x + 1 / x - Real.sqrt 3 = ((3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1) / x := by
          field_simp
          ring
        rw [h64]
        have h65 : ((3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1) ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 2 * Real.sqrt 3 / 3), sq_nonneg (x ^ 2), Real.sqrt_nonneg 3]
        have h66 : x > 0 := hx
        have h67 : ((3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1) / x ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals nlinarith
        linarith
      linarith
    have h7 : (3 / 4) * x + 1 / x - 1 ≥ Real.sqrt 3 - 1 := by
      linarith
    linarith