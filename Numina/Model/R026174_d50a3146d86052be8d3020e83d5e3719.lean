import Mathlib

theorem algebra_195644 {α β b : ℝ} (hroots : α^2 + b * α - 2 = 0 ∧ β^2 + b * β - 2 = 0)
    (hα : α > 1) (hβ : β < -1) (hb : ∃ n : ℤ, b = n) :
    b = 0 := by
  rcases hroots with ⟨ha, hb_eq⟩
  rcases hb with ⟨n, hbn⟩
  have h1 : b - 1 < 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hα), sq_pos_of_neg (show β + 1 < 0 by linarith), 
          sq_nonneg (α - β), sq_nonneg (α + β + b)]
  have h2 : -b - 1 < 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hα), sq_pos_of_neg (show β + 1 < 0 by linarith), 
          sq_nonneg (α - β), sq_nonneg (α + β + b)]
  have hb1 : b > -1 := by linarith
  have hb2 : b < 1 := by linarith
  have h3 : (n : ℝ) > -1 := by linarith [hbn, hb1]
  have h4 : (n : ℝ) < 1 := by linarith [hbn, hb2]
  have hn : n = 0 := by 
    have h3' : n > -1 := by
      by_contra h
      push_neg at h 
      have h4' : n ≤ -1 := by omega
      have h5 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h4'
      nlinarith 
    have h4' : n < 1 := by
      by_contra h
      push_neg at h 
      have h5 : n ≥ 1 := by omega
      have h6 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h5 
      nlinarith 
    omega 
  have h5 : (b : ℝ) = (0 : ℝ) := by 
    linarith [hbn, show (n : ℝ) = (0 : ℝ) by exact_mod_cast hn]
  linarith 
  all_goals nlinarith 
  all_goals nlinarith