import Mathlib

theorem number_theory_37479 (n : ℕ) (hn : n ≠ 0) :
    ∃ q : ℚ, Real.sqrt (1 + 1 / n ^ 2 + 1 / (n + 1) ^ 2) = q := by
  use (↑n ^ 2 + (↑n : ℚ) + 1) / ((↑n : ℚ) * ((↑n + 1 : ℚ)))
  have h1 : (1 : ℝ) + 1 / n ^ 2 + 1 / (n + 1) ^ 2 = ((↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ)))) ^ 2 := by
    have h3 : (↑n : ℝ) > 0 := by
      have h3 : (↑n : ℝ) ≥ 1 := by
        exact_mod_cast show n ≥ 1 by omega
      linarith
    have h4 : (↑n + 1 : ℝ) > 0 := by
      have h3 : (↑n : ℝ) > 0 := h3
      linarith
    field_simp [show (↑n : ℝ) ≠ 0 by linarith, show ((↑n + 1 : ℝ)) ≠ 0 by linarith]
    ring_nf
  have h3 : Real.sqrt (1 + 1 / n ^ 2 + 1 / (n + 1) ^ 2) = (↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ))) := by
    rw [h1]
    have h4 : Real.sqrt (((↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ)))) ^ 2) = ((↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ))) ) := by
      have h5 : (↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ))) ≥ 0 := by
        have h3 : (↑n : ℝ) > 0 := by
          have h3 : (↑n : ℝ) ≥ 1 := by
            exact_mod_cast show n ≥ 1 by omega
          linarith
        have h4 : (↑n + 1 : ℝ) > 0 := by
          have h3 : (↑n : ℝ) > 0 := h3
          linarith
        positivity
      rw [Real.sqrt_sq (show 0 ≤ ((↑n ^ 2 + (↑n : ℝ) + 1) / ((↑n : ℝ) * ((↑n + 1 : ℝ))) ) by exact_mod_cast h5)]
    rw [h4]
  norm_num at h3 ⊢
  all_goals
    exact_mod_cast h3