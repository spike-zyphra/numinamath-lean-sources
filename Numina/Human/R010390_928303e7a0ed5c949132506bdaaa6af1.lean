import Mathlib

/- Two friends are playing tic-tac-toe. If Amy wins $\frac{3}{8}$ of the time, Lily wins $\frac{3}{10}$ of the time, and they tie the rest of the time, then what fraction of the time do they tie? -/
theorem algebra_14662 (a l t : ℝ)
    (ha : a = 3 / 8) (hl : l = 3 / 10) (ht : t = 1 - a - l) :
    t = 13 / 40 := by 
  subst_vars
  ring