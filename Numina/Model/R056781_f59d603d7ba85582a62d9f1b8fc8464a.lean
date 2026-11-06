import Mathlib

theorem number_theory_6376 (m : ℕ) (hm : 0 < m) :
    ∃ x0 y0 : ℝ, 0 < abs x0 ∧ abs x0 ≤ Real.sqrt m ∧ 0 < abs y0 ∧ abs y0 < Real.sqrt m := by
  use Real.sqrt (m : ℝ) / 2
  use Real.sqrt (m : ℝ) / 2
  have h1 : 0 < (m : ℝ) := by exact_mod_cast hm
  have h2 : 0 < Real.sqrt (m : ℝ) := by positivity
  have hx1 : 0 < abs (Real.sqrt (m : ℝ) / 2) := by
    have h3 : Real.sqrt (m : ℝ) / 2 > 0 := by positivity
    rw [abs_of_pos (by positivity)]
    all_goals linarith
  have hx2 : abs (Real.sqrt (m : ℝ) / 2) ≤ Real.sqrt (m : ℝ) := by
    have h3 : abs (Real.sqrt (m : ℝ) / 2) = Real.sqrt (m : ℝ) / 2 := by
      rw [abs_of_nonneg]
      positivity
    rw [h3]
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hy1 : 0 < abs (Real.sqrt (m : ℝ) / 2) := hx1
  have hy2 : abs (Real.sqrt (m : ℝ) / 2) < Real.sqrt (m : ℝ) := by
    have h3 : abs (Real.sqrt (m : ℝ) / 2) = Real.sqrt (m : ℝ) / 2 := by
      rw [abs_of_nonneg]
      positivity
    rw [h3]
    have h4 : Real.sqrt (m : ℝ) > 0 := by positivity
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < m by exact_mod_cast hm)]
  exact ⟨hx1, hx2, hy1, hy2⟩