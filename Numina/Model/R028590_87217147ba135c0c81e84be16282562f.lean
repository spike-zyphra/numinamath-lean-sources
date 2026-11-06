import Mathlib

theorem algebra_15263 {G H : ℤ} (h : ∀ x : ℝ, x ≠ -5 → x ≠ 0 → x ≠ 4 → (G / (x + 5) + H / (x ^ 2 - 4 * x))  = (x ^ 2 - 2 * x + 10) / (x ^ 3 + x ^ 2 - 20 * x)) :
    H / G = 2 := by
  have eq1 := h 1 (by norm_num) (by norm_num) (by norm_num)
  have eq2 := h 2 (by norm_num) (by norm_num) (by norm_num)
  have eq3 := h 3 (by norm_num) (by norm_num) (by norm_num)
  have eq4 := h 6 (by norm_num) (by norm_num) (by norm_num)
  field_simp at eq1 eq2 eq3 eq4
  ring_nf at eq1 eq2 eq3 eq4 
  have h1 : (G : ℝ) = 1 := by
    nlinarith 
  have h2 : (H : ℝ) = 2 := by 
    nlinarith
  have hG : G = 1 := by
    exact_mod_cast h1 
  have hH : H = 2 := by 
    exact_mod_cast h2
  norm_num [hG, hH]