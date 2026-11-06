import Mathlib

theorem algebra_267544 (x : ℝ) (hx : x < -2) :
    min (min (min (min x (x + 2)) (1 / 2 * x)) (x - 2)) (2 * x) = 2 * x := by 
  have h1 : x < -2 := hx
  have h2 : 2 * x < x := by 
    linarith
  have h3 : 2 * x < x + 2 := by 
    linarith [h2]
  have h4 : 2 * x < 1 / 2 * x := by
    linarith [h1]
  have h5 : 2 * x < x - 2 := by
    linarith
  have h6 : min x (x + 2) = x := by 
    apply min_eq_left 
    linarith
  have h7 : min (min x (x + 2)) (1 / 2 * x) = x := by
    rw [h6]
    apply min_eq_left 
    linarith [h4]
  have h8 : min (min (min x (x + 2)) (1 / 2 * x)) (x - 2) = x - 2 := by
    rw [h7]
    apply min_eq_right 
    linarith
  have h9 : min (min (min (min x (x + 2)) (1 / 2 * x)) (x - 2)) (2 * x) = 2 * x := by
    rw [h8]
    apply min_eq_right 
    linarith [h5]
  exact h9