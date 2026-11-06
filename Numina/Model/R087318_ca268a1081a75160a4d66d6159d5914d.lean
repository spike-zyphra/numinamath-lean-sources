import Mathlib.Tactic

theorem algebra_815
    (a b c t_catchup_b t_catchup_c t_catchup_a : ℝ) 
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : t_catchup_b = 2) (h2 : t_catchup_c = 25) (h3 : t_catchup_a = t_catchup_b / (1 - a / b)) (h4 : t_catchup_a = t_catchup_c / (1 - a / c)) (h5 : t_catchup_b / t_catchup_c = 3 / 2) : 60 * a = 42 := by 
  have h6 : t_catchup_b / t_catchup_c = 2 / 25 := by 
    rw [h1, h2]
    all_goals linarith
  linarith