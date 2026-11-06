import Mathlib

theorem algebra_274071 (xiao_bing xiao_bing_mother : ℕ) (h : xiao_bing = 7) (h' : xiao_bing_mother = 35) :
    ∃ n, xiao_bing_mother + n = 3 * (xiao_bing + n) := by 
  subst h h'
  use 7
  all_goals norm_num