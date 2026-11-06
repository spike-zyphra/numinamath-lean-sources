import Mathlib

theorem algebra_157985 (p : ℝ) (hp : p ∈ Set.Icc 0 1) (h : (1 - p) / p = 1 + p / (1 - p)) :
    p = (3 - Real.sqrt 5) / 2 := by
  rcases hp with ⟨hp0, hp1⟩
  have h3 : p ≠ 0 := by
    by_contra h3
    rw [h3] at h
    field_simp at h
    <;> norm_num at h
    all_goals nlinarith
  have h2 : (1 - p) ≠ 0 := by
    by_contra h2
    have hp1' : p = 1 := by linarith
    rw [hp1'] at h
    norm_num at h
    all_goals nlinarith
    all_goals norm_num at h <;> norm_num at h3 <;> norm_num at hp0 <;> norm_num at hp1 <;> linarith
  field_simp [h3, h2] at h
  have h4 : p ^ 2 - 3 * p + 1 = 0 := by
    nlinarith [h]
  have h5 : p ^ 2 - 3 * p + 1 = (p - (3 + Real.sqrt 5) / 2) * (p - (3 - Real.sqrt 5) / 2) := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  rw [h5] at h4
  cases' (mul_eq_zero.1 h4) with h6 h7
  · -- Case where p = (3 + sqrt 5)/2
    have h8 : p = (3 + Real.sqrt 5) / 2 := by linarith
    have h9 : p > (1 : ℝ) := by
      have h10 : Real.sqrt 5 > 2 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    linarith [hp1, h9]
  · -- Case where p = (3 - sqrt 5)/2
    linarith
  all_goals nlinarith