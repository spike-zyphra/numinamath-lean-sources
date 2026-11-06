import Mathlib

open Real

theorem algebra_97855 {a b c d e : ℝ} (ha : a < b) (hb : b < c) (hc : c < d)
    (hd : d < e) :
    max (max a (min b c)) (min d (min a e)) = b := by 
  have h1 : min b c = b := by
    apply min_eq_left
    linarith
  have h2 : max a (min b c) = b := by
    rw [h1]
    apply max_eq_right
    linarith
  have h3 : min a e = a := by 
    apply min_eq_left 
    linarith
  have h4 : min d (min a e) = a := by 
    rw [h3]
    apply min_eq_right 
    linarith
  rw [h2, h4]
  apply max_eq_left 
  linarith