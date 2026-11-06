import Mathlib

theorem algebra_193707 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h1 : (b / 6 : ℝ) + (g / 7 : ℝ) = 48 + 50)
    (h2 : (g - (g / 7 : ℝ)) = 2 * (b - (b / 6 : ℝ))) :
    b = 72 ∧ g = 72 := by
  have eq3 : (7 * (b : ℝ) + 6 * (g : ℝ)) = 4116 := by 
    have eq1 : (b / 6 : ℝ) + (g / 7 : ℝ) = 48 + 50 := h1 
    field_simp at eq1 ⊢
    linarith
  have eq4 : (7 * (b : ℕ) + 6 * (g : ℕ)) = 4116 := by 
    exact_mod_cast eq3
  have eq5 : (18 * (g : ℝ) ) = (35 * (b : ℝ) ) := by 
    have eq6 : (g - (g / 7 : ℝ) ) = 2 * (b - (b / 6 : ℝ) ) := by
      linarith [h2]
    field_simp at eq6 ⊢ 
    nlinarith
  have eq6 : (18 * (g : ℕ) ) = (35 * (b : ℕ) ) := by 
    exact_mod_cast eq5 
  have h7 : b ≤ 588 := by 
    omega
  have h8 : g ≤ 686 := by
    omega
  have h6 : b = 72 := by
    omega
  have h7 : g = 72 := by
    omega
  tauto