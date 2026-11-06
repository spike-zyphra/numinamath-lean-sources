import Mathlib

theorem inequalities_597362 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    ((1 + a) / (1 - a)) * ((1 + b) / (1 - b)) ≥ 3^2 := by 
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have h1 : b = 1 - a := by linarith 
  have ha2 : a < 1 := by
    nlinarith
  have hb2 : b < 1 := by
    nlinarith
  have h1a : 1 - a = b := by linarith 
  have h1b : 1 - b = a := by linarith 
  have h2 : ((1 + a) / (1 - a)) * ((1 + b) / (1 - b)) = ((1 + a) * (1 + b)) / (a * b) := by 
    have hc : 1 - a = b := by linarith 
    have hd : 1 - b = a := by linarith 
    rw [hc, hd]
    <;> field_simp [(show b > 0 by linarith), (show a > 0 by linarith)]
    <;> ring
  rw [h2]
  have h3 : (1 + a) * (1 + b) ≥ 9 * (a * b) := by
    have h4 : a + b = 1 := by linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
        mul_pos ha hb, mul_pos ha (show 0 < 1 - a by nlinarith), 
        mul_pos hb (show 0 < 1 - b by nlinarith)]
  have h4 : a * b > 0 := by
    positivity
  have h7 : ((1 + a) * (1 + b)) / (a * b) ≥ 9 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [h3]
  norm_num at h7 ⊢
  all_goals linarith