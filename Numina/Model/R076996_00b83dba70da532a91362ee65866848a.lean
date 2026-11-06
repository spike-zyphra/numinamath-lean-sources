import Mathlib

theorem algebra_280905 {a b c d : ℕ}
    (ha : a + b = 625) (hb : c + d = 748)
    (h1 : c = (1 + 24 / 100 : ℝ) * a) (h2 : b = (1 - 15 / 100 : ℝ) * d) :
    c = 248 := by

  have eq1 : (a : ℝ) + (b : ℝ) = (625 : ℝ) := by
    exact_mod_cast ha
  have eq2 : (c : ℝ) + (d : ℝ) = (748 : ℝ) := by
    exact_mod_cast hb
  have eq3 : (c : ℝ) = (1 + 24 / 100 : ℝ) * (a : ℝ) := by
    exact_mod_cast h1
  have eq4 : (b : ℝ) = (1 - 15 / 100 : ℝ) * (d : ℝ) := by
    exact_mod_cast h2

  have eq5 : (a : ℝ) + (0.85 : ℝ) * (d : ℝ) = (625 : ℝ) := by
    have h3 : (b : ℝ) = (0.85 : ℝ) * (d : ℝ) := by 
      rw [eq4]
      all_goals ring_nf
    rw [h3] at eq1
    linarith
  have eq6 : (1.24 : ℝ) * (a : ℝ) + (d : ℝ) = (748 : ℝ) := by
    have h4 : (c : ℝ) = (1.24 : ℝ) * (a : ℝ) := by
      rw [eq3]
      all_goals ring_nf
    rw [h4] at eq2
    linarith
  have eq7 : (a : ℝ) = (200 : ℝ) := by
    norm_num at eq5 eq6 ⊢
    linarith
  have hc : (c : ℝ) = (248 : ℝ) := by
    rw [eq3]
    rw [eq7]
    norm_num
  exact_mod_cast hc