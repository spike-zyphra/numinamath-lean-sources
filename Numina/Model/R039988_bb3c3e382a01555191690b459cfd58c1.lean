import Mathlib

theorem algebra_10268 (x : ℝ) (hxpos : 0 < x) (harith : ∃ d, x ^ 2 = 1 ^ 2 + d ∧ 3 ^ 2 = x ^ 2 + d) :
    x = √5 := by
  rcases harith with ⟨d, h1, h2⟩
  have eq1 : x^2 = 1 + d := by
    linarith 
  have eq2 : 9 = x^2 + d := by
    nlinarith 
  have h3 : d = 4 := by
    nlinarith [eq1, eq2]
  have h4 : x^2 = 5 := by 
    rw [h3] at eq1
    linarith 
  have h5 : x = Real.sqrt 5 := by
    have h6 : x > 0 := hxpos
    have h7 : x^2 = 5 := h4
    have h8 : x = Real.sqrt 5 := by
      rw [← h7]
      field_simp
    exact h8
  rw [h5]
  all_goals norm_num