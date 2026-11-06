import Mathlib

theorem algebra_401 {a b c d : ℝ} (ha : a ≠ 0) (h : ∀ k ∈ ({1, 2, 3, 4} : Finset ℝ), a * k ^ 3 + b * k ^ 2 + c * k + d = 1 / k) :
    (c - d) / (a + b) = -85 / 9 := by

  have eq1 := h 1 (by simp)
  have eq2 := h 2 (by norm_num)
  have eq3 := h 3 (by norm_num)
  have eq4 := h 4 (by norm_num)

  have eq1' : a + b + c + d = 1 := by
    norm_num at eq1 ⊢
    linarith

  have eq2' : 8 * a + 4 * b + 2 * c + d = 1 / 2 := by 
    norm_num at eq2 ⊢ 
    linarith

  have eq3' : 27 * a + 9 * b + 3 * c + d = 1 / 3 := by
    norm_num at eq3 ⊢ 
    linarith

  have eq4' : 64 * a + 16 * b + 4 * c + d = 1 / 4 := by
    norm_num at eq4 ⊢ 
    linarith

  have eq5 : 7 * a + 3 * b + c = -1 / 2 := by
    linarith

  have eq6 : 19 * a + 5 * b + c = -1 / 6 := by
    linarith

  have eq7 : 37 * a + 7 * b + c = -1 / 12 := by 
    linarith

  have eq8 : 12 * a + 2 * b = 1 / 3 := by 
    linarith

  have eq9 : 18 * a + 2 * b = 1 / 12 := by
    linarith

  have eq10 : 6 * a = -1 / 4 := by 
    linarith

  have ha' : a = -1 / 24 := by 
    linarith

  have hb : b = 5 / 12 := by 
    linarith [ha', eq8]

  have hc : c = -35 / 24 := by 
    linarith [ha', hb, eq5]

  have hd : d = 25 / 12 := by 
    linarith [ha', hb, hc, eq1']

  have h11 : c - d = -85 / 24 := by 
    linarith [hc, hd]

  have h12 : a + b = 9 / 24 := by 
    linarith [ha', hb]

  have h13 : (c - d) / (a + b) = -85 / 9 := by 
    rw [h11, h12]
    norm_num

  exact h13
  all_goals linarith