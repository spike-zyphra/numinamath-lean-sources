import Mathlib
open Real

theorem algebra_190678 : ∏' (n : ℕ), (2 : ℝ) ^ (1 / (n + 1).factorial : ℝ) = 2 ^ (exp 1 - 1) := by
  have h₀ : HasSum (fun (n : ℕ) => (1 : ℝ) ^ n / n.factorial) (exp 1) := by
    rw [exp_eq_exp_ℝ]
    apply NormedSpace.expSeries_div_hasSum_exp
  replace h₀ : HasSum (fun (n : ℕ) => log ((2 : ℝ) ^ (1 / (n + 1).factorial : ℝ))) (log (2 ^ (exp 1 - 1))) := by
    have (n : ℕ) : log ((2 : ℝ) ^ ((1 : ℝ) / (n + 1).factorial)) = log 2 * (1 / (n + 1).factorial) := by
      rw [Real.log_rpow (by norm_num)]
      ac_rfl
    simp [this, Real.log_rpow (show 0 < 2 by norm_num), -one_div]
    rw [mul_comm]
    apply HasSum.mul_left
    rw [@hasSum_nat_add_iff _ _ (rexp 1 - 1) _ _ (fun (n : ℕ) => (1 / n.factorial : ℝ)) 1]
    simp [-one_div] at h₀ ⊢
    exact h₀
  have h₁ : ∀ n, 0 < (2 : ℝ) ^ ((n + 1).factorial : ℝ)⁻¹ := by
    intro n
    apply Real.rpow_pos_of_pos (by norm_num)
  replace h₀ : HasProd (fun (n : ℕ) => (2 : ℝ) ^ (1 / (n + 1).factorial : ℝ)) (exp (log (2 ^ (exp 1 - 1)))) := h₀.rexp.congr (by simp [exp_log, h₁])
  convert HasProd.tprod_eq h₀ using 1
  rw [exp_log (by apply Real.rpow_pos_of_pos (by norm_num))]
