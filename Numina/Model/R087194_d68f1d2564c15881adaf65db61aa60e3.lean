import Mathlib

theorem inequalities_149453 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    a^2 / (a + 1) + b^2 / (b + 1) ≥ 1 / 3 := by
  have hb_eq : b = 1 - a := by linarith
  rw [hb_eq]
  have h1 : 0 < a := by linarith
  have h2 : a < 1 := by 
    have hb' : (1 - a) > 0 := by linarith
    linarith
  have ha1 : a + 1 > 0 := by linarith
  have ha2 : (1 - a) + 1 > 0 := by linarith 
  have h3 : a^2 / (a + 1) + (1 - a)^2 / ((1 - a) + 1) - 1 / 3 ≥ 0 := by 
    have pos1 : a + 1 > 0 := ha1
    have pos2 : (1 - a) + 1 > 0 := ha2
    have h4 : a^2 / (a + 1) + (1 - a)^2 / ((1 - a) + 1) - 1 / 3 =
        (a^2 * ((1 - a) + 1) + (1 - a)^2 * (a + 1) - 1 / 3 * ((a + 1) * ((1 - a) + 1)) ) / ((a + 1) * ((1 - a) + 1)) := by 
      field_simp
      <;> ring_nf <;> field_simp
      <;> norm_num
      <;> linarith
      <;> norm_num <;> field_simp
      <;> linarith
    rw [h4]
    have pos3 : (a + 1) * ((1 - a) + 1) > 0 := by positivity
    apply div_nonneg 
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a - (1 - a))]
    all_goals positivity 
  linarith