import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem algebra_8245 (m : ℝ) :
  (∀ x : ℝ, 2 * abs x = m * x - 3 → x ≥ 0) ↔ m ≥ -2 := by
  constructor
  · -- Assume ∀ x, 2 * |x| = m * x - 3 → x ≥ 0, prove m ≥ -2
    intro h
    by_contra h1
    push_neg at h1
    have h2 : ∃ y : ℝ, y < 0 ∧ 2 * abs y = m * y - 3 := by
      use 3 / (2 + m)
      constructor
      · -- Show that 3 / (2 + m) < 0
        apply div_neg_of_pos_of_neg
        · norm_num -- 3 > 0
        · -- Show that 2 + m < 0 from m < -2
          linarith
      · -- Verify the equation
        have h3 : abs (3 / (2 + m)) = - (3 / (2 + m)) := by
          rw [abs_of_neg]
          · -- Show 3 / (2 + m) < 0
            apply div_neg_of_pos_of_neg
            all_goals linarith
          all_goals linarith
        rw [h3]
        field_simp [(show 2 + m ≠ 0 by linarith)]
        <;> nlinarith
        <;> try linarith
        all_goals nlinarith
    obtain ⟨y, hy⟩ := h2
    have hy1 : y < 0 := hy.1
    have hy2 : 2 * abs y = m * y - 3 := hy.2
    have h4 := h y hy2
    linarith -- contradiction with y < 0 and h4 : y ≥ 0
  · -- Show that m ≥ -2 implies ∀ x : ℝ, 2 * abs x = m * x - 3 → x ≥ 0
    intro hm
    intro x h1
    by_contra h2
    push_neg at h2
    have h3 : abs x = - x := by
      rw [abs_of_neg]
      linarith
    rw [h3] at h1
    have : m < -2 := by
      nlinarith [h2, sq_nonneg (x), sq_nonneg (m + 2)]
      all_goals nlinarith
    nlinarith
    all_goals nlinarith