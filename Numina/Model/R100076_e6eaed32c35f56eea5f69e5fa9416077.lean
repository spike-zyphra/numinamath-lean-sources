import Mathlib

theorem algebra_123175 (total_money : ℕ) (h : total_money = (500^2 + 4 * 500 + 3) * 498^2 - 500^2 * 503 * 497) :
    total_money < 2019 := by 
  norm_num [h]