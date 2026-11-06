import Mathlib

theorem algebra_168015 {m1 m2 e1 e2 : ℝ}
    (hm1 : m1 > 0) (hm2 : m2 > 0)
    (he1 : e1 > 0) (he2 : e2 > 0)
    (hmass : m2 = m1 * (1 - 25 / 100)) (hedge : e2 = e1 * (1 + 25 / 100)) :
    |(m2 / e2^3 - m1 / e1^3)| / (m1 / e1^3) = 61.6 / 100 := by
  have h1 : m2 = m1 * (3 / 4) := by
    rw [hmass]
    ring_nf
    <;> norm_num
    all_goals linarith

  have h2 : e2 = e1 * (5 / 4) := by
    rw [hedge]
    ring_nf
    <;> norm_num
    all_goals linarith
  
  have eq1 : m2 / e2^3 - m1 / e1^3 = (m1 / e1^3) * (-77 / 125) := by
    rw [h1, h2]
    field_simp [(show e1 ≠ 0 by nlinarith), (show e1 * (5/4) ≠ 0 by nlinarith), (show (e1 * (5/4))^3 ≠ 0 by positivity)]
    <;> ring_nf
    <;> field_simp [(show e1 ≠ 0 by nlinarith), (show e1 * (5/4) ≠ 0 by nlinarith), (show (e1 * (5/4))^3 ≠ 0 by positivity)]
    <;> nlinarith [sq_pos_of_pos hm1, sq_pos_of_pos he1]
    <;> ring_nf
    <;> nlinarith
  
  have h4 : |m2 / e2^3 - m1 / e1^3| = (m1 / e1^3) * (77 / 125) := by
    have h5 : m2 / e2^3 - m1 / e1^3 < 0 := by
      rw [eq1]
      have h7 : m1 / e1^3 > 0 := by
        apply div_pos
        linarith
        positivity
      nlinarith
    rw [abs_of_neg h5]
    all_goals nlinarith [eq1]
  
  have h7 : m1 / e1^3 > 0 := by
    apply div_pos
    linarith
    positivity
  
  rw [h4]
  field_simp [(show e1 ≠ 0 by nlinarith), h7]
  <;> norm_num
  <;> ring_nf
  <;> norm_num
  all_goals nlinarith
  <;> norm_num
  <;> nlinarith
  all_goals positivity
  all_goals nlinarith