import Mathlib

theorem algebra_244156 {f g : ℝ → ℝ}
    (hf : f = fun x => 1 / x) (hg : g = fun x => -1 / (x + 2)) :
    ∀ x, g x = f (-x - 2) := by
  intro x
  rw [hg, hf]
  have h : -1 / (x + 2 : ℝ) = 1 / (-x - 2 : ℝ) := by
    by_cases h5 : (x + 2 : ℝ) = 0
    · -- case if x + 2 = 0
      have h6 : (-x - 2 : ℝ) = 0 := by
        have h7 : x = -2 := by linarith
        rw [h7]
        norm_num
      simp [h5, h6]
    · -- case if x + 2 ≠ 0
      have h10 : (x + 2 : ℝ) ≠ 0 := h5
      have h11 : (-x - 2 : ℝ) ≠ 0 := by
        intro h12
        apply h10
        have h13 : (x + 2 : ℝ) = 0 := by
          have h4 : (-x - 2 : ℝ) = 0 := by
            exact h12
          have h5 : x = -2 := by linarith
          rw [h5]
          norm_num
        exact h13
      field_simp [h10, h11]
      all_goals ring
  simpa using h