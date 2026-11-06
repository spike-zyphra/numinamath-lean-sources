import Mathlib

open Real

theorem algebra_13061 {α β : ℝ} (h : α ≠ β) (h1 : 0 < α) (h2 : 0 < β)
    (h3 : log (6 * α) * log (α / 1866) = 2017) (h4 : log (6 * β) * log (β / 1866) = 2017) :
    α * β = 311 := by
  have h5 : log (6 * α) = log 6 + log α := by 
    rw [log_mul (by positivity) (by positivity)]
  have h6 : log (α / 1866) = log α - log 1866 := by 
    rw [log_div (by positivity) (by norm_num)]
  have h7 : log (6 * β) = log 6 + log β := by 
    rw [log_mul (by positivity) (by positivity)]
  have h8 : log (β / 1866) = log β - log 1866 := by 
    rw [log_div (by positivity) (by norm_num)]
  rw [h5, h6] at h3
  rw [h7, h8] at h4
  have h9 : (log α)^2 + (log 6 - log 1866) * (log α) - (log 6 * log 1866 + 2017) = 0 := by
    nlinarith
  have h10 : (log β)^2 + (log 6 - log 1866) * (log β) - (log 6 * log 1866 + 2017) = 0 := by
    nlinarith
  have h12 : (log α - log β) * (log α + log β + (log 6 - log 1866)) = 0 := by
    nlinarith [h9, h10, sq_pos_of_ne_zero (show (log α - log β) ≠ 0 by
        intro h'
        apply h
        have : α = β := by
          have : log α = log β := by 
            nlinarith
          have h5 : α = β := by
            exact Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) this
          exact h5
        exact this
      )
    ]
  cases (mul_eq_zero.mp h12) with
  | inl h14 =>
    exfalso
    apply h
    have h5 : log α = log β := by
      linarith
    have : α = β := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) h5
    contradiction
  | inr h15 =>
    have h14 : log α + log β = log 311 := by 
      have h15' : log α + log β = - (log 6 - log 1866) := by 
        nlinarith
      have h311 : log 311 = log (1866 / 6) := by 
        norm_num [log_div]
      have h314 : log (1866 / 6) = log 1866 - log 6 := by 
        rw [log_div (by norm_num) (by norm_num)]
      linarith [h15', h311, h314]
    have h311 : log (α * β) = log 311 := by 
      rw [log_mul (by positivity) (by positivity)]
      linarith [h14]
    have h300 : α * β = 311 := by 
      have h_pos : α * β > 0 := by positivity
      have h311' : log (α * β) = log 311 := by 
        rw [log_mul (by positivity) (by positivity)]
        linarith [h14]
      have : α * β = 311 := by 
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos) (Set.mem_Ioi.mpr (show 0 < (311: ℝ) by norm_num)) h311'
      exact this 
    exact h300