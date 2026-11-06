import Mathlib

theorem algebra_290739 (x y z : ℕ) (h : x + y + z = 220) (h1 : y = (220 : ℝ) * 40 / 100) (h2 : z = (220 : ℝ) * 40 / 100) :
    x = 44 := by
  have h1' : (y : ℝ) = (88 : ℝ) := by 
    norm_num at h1 ⊢
    linarith

  have hy : y = 88 := by
    exact_mod_cast h1'

  have h2' : (z : ℝ) = (88 : ℝ) := by
    norm_num at h2 ⊢
    linarith

  have hz : z = 88 := by
    exact_mod_cast h2'

  omega