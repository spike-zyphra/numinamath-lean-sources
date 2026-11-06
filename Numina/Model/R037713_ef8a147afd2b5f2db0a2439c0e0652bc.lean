import Mathlib

open Real

theorem inequalities_156632 {n k : ℝ} (hn : 0 < n) (hk : 0 < k) :
    ((n * exp 1) / k) ^ k ≤ exp n := by
  have h1 : ((n * exp 1) / k) ^ k ≤ exp n := by
    have h2 : 0 < (n * exp 1) / k := by
      apply div_pos
      all_goals
      nlinarith [Real.exp_pos 1]
    have h3 : ((n * exp 1) / k) ^ k ≥ 0 := by positivity
    have h4 : exp n ≥ 0 := by positivity
    have h10 : k * (log ((n * exp 1) / k)) ≤ n := by
      have h20 : k * (log ((n * exp 1) / k)) = k * (log (n * exp 1) - log k) := by
        rw [log_div (by positivity) (by positivity)]
      have h21 : log (n * exp 1) = log n + log (exp 1) := by
        rw [log_mul (by positivity) (by positivity)]
      have h22 : log (exp 1) = (1 : ℝ) := by
        rw [log_exp]
      rw [h20, h21, h22]
      have h40 : k * (log n - log k) ≤ n - k := by
        have h443 : log (n / k) = log n - log k := by
          rw [log_div (by positivity) (by positivity)]
        have h43 : k * log (n / k) ≤ n - k := by
          have h44 : log (n / k) ≤ (n / k - 1) := by
            have h45 : log (n / k) ≤ (n / k - 1) := by
              apply Real.log_le_sub_one_of_pos
              positivity
            linarith
          have h446 : k * ((n / k - 1)) = n - k := by
            field_simp [show k ≠ 0 by nlinarith]
            all_goals
            nlinarith
          have h449 : k * log (n / k) ≤ k * ((n / k - 1)) := by
            apply mul_le_mul_of_nonneg_left
            linarith
            all_goals
            nlinarith
          rw [h446] at h449
          linarith
        rw [show log n - log k = log (n / k) by
          have h443 : log (n / k) = log n - log k := by
            rw [log_div (by positivity) (by positivity)]
          linarith
        ]
        linarith
      linarith
    have h7 : (( (n * exp 1 ) / k ) ^ k ) = exp (k * log ((n * exp 1 ) / k ) ) := by
      rw [show k * log ((n * exp 1 ) / k ) = (log (( (n * exp 1 ) / k ) ^ k ) ) by 
        have h10 : log (( (n * exp 1 ) / k ) ^ k ) = k * log (( (n * exp 1 ) / k ) ) := by
          rw [log_rpow]
          all_goals
            positivity
        linarith
      ]
      rw [exp_log]
      all_goals
        positivity
    rw [h7]
    have h9'9 : exp (k * log ((n * exp 1) / k)) ≤ exp (n) := by
      apply Real.exp_le_exp_of_le 
      linarith
    linarith
  linarith