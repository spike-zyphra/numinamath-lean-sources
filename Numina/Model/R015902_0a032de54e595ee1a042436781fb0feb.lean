import Mathlib

open Real
open scoped BigOperators

theorem inequalities_68686 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 2) :
  1 + a * b * c < a * b + b * c + c * a ∧ a * b + b * c + c * a ≤ 28 / 27 + a * b * c := by
  constructor
  · -- Prove the first part: $1 + a * b * c < a * b + b * c + c * a$
    have h1 : a * b + b * c + c * a - (1 + a * b * c) > 0 := by
      have h2 : 0 < a * b := mul_pos ha hb
      have h3 : 0 < b * c := mul_pos hb hc
      have h4 : 0 < c * a := mul_pos hc ha
      have h5 : 0 < a * b * c := by positivity
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
        sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
        mul_pos h2 h3, mul_pos h2 h4, mul_pos h3 h4]
    linarith
  · -- Prove the second part: $a * b + b * c + c * a \leq \frac{28}{27} + a * b * c$
    have h2 : a * b + b * c + c * a - a * b * c ≤ 28 / 27 := by
      have h1a : c = 2 - a - b := by linarith
      rw [h1a]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
        mul_pos ha hb, 
        mul_pos ha (show (2 - a - b) > 0 by nlinarith), 
        mul_pos hb (show (2 - a - b) > 0 by nlinarith), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h)]
    linarith