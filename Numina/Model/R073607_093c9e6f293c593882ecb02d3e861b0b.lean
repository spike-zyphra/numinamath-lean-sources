import Mathlib

theorem number_theory_4011 (N : ℕ) (hN : N > 0) (shiny blue : ℕ)
    (hshiny : shiny = N * (3 / 4 : ℚ)) (hblue : blue = N * (1 / 2 : ℚ)) :
    (shiny + blue - N) * (1 / N : ℚ) = 25 / 100 := by
  have h1 : (shiny : ℚ) = (N : ℚ) * (3 / 4 : ℚ) := by
    exact_mod_cast hshiny
  have h2 : (blue : ℚ) = (N : ℚ) * (1 / 2 : ℚ) := by
    exact_mod_cast hblue
  have eq1 : (shiny : ℚ) + (blue : ℚ) - (N : ℚ) = (1 / 4 : ℚ) * (N : ℚ) := by
    rw [h1, h2]
    linarith
  have eq2 : ((shiny : ℚ) + (blue : ℚ) - (N : ℚ)) * ((1 / (N : ℚ)) : ℚ) = (1 / 4 : ℚ) := by
    rw [eq1]
    have hNne : (N : ℚ) ≠ 0 := by
      exact_mod_cast show N ≠ 0 by omega
    field_simp [hNne]
    all_goals linarith
  norm_num at eq2 ⊢
  exact_mod_cast eq2