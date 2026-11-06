import Mathlib

theorem algebra_199086 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (hprob : (b : ℝ) / (b + g) = 2 / 3 * (g : ℝ) / (b + g)) :
    b / (b + g) = 2 / 5 := by
  have h1 : (b : ℝ) > 0 := by
    exact_mod_cast show (0 : ℕ) < b by 
      omega
  have h2 : (g : ℝ) > 0 := by
    exact_mod_cast show (0 : ℕ) < g by
      omega
  have h3 : (b + g : ℝ) > 0 := by
    linarith
  have eq1 : (b : ℝ) = 2 / 3 * (g : ℝ) := by
    have h4 : (b + g : ℝ) ≠ 0 := by
      positivity
    field_simp [h4] at hprob ⊢
    nlinarith
  have eq2 : 3 * (b : ℝ) = 2 * (g : ℝ) := by
    nlinarith
  have h5 : 3 * b = 2 * g := by
    have h22 : (3 * (b : ℝ) = 2 * (g : ℝ)) := eq2
    norm_cast at h22 ⊢
    all_goals nlinarith
  have eq3 : b * 5 = 2 * (b + g) := by
    omega
  norm_num at eq3 ⊢
  all_goals omega