import Mathlib

theorem algebra_167456 {b g : ℕ} (hb : b > 0) (hg : g > 0)
    (h : b * 3 = g * 2) :
    (b : ℝ) / (b + g) = 2 / 5 := by

  have h1 : (b : ℝ) * 3 = (g : ℝ) * 2 := by
    exact_mod_cast h
  
  have h2 : (b : ℝ) = (2 : ℝ) / 3 * (g : ℝ) := by 
    linarith
  
  have h3 : (b : ℝ) + (g : ℝ) = (5 : ℝ) / 3 * (g : ℝ) := by
    have h4 : (b : ℝ) = (2 : ℝ) / 3 * (g : ℝ) := by 
      linarith
    nlinarith [h4]

  have hg2 : (g : ℝ) > 0 := by 
    have h1 : g > 0 := hg
    exact_mod_cast h1

  have h4 : (b : ℝ) + (g : ℝ) > 0 := by
    have h5 : (g : ℝ) > 0 := hg2
    nlinarith [h3]

  have h5 : (b : ℝ) / ((b : ℝ) + (g : ℝ)) = (2 : ℝ) / 5 := by
    have h6 : (b : ℝ) = (2 : ℝ) / 3 * (g : ℝ) := h2
    have h7 : (b : ℝ) + (g : ℝ) = (5 : ℝ) / 3 * (g : ℝ) := h3
    have h8 : (b : ℝ) + (g : ℝ) > 0 := h4
    have h9 : (g : ℝ) > 0 := hg2
    field_simp [h8]
    <;> nlinarith [h1]

  exact h5