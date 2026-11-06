import Mathlib

/- Compute

$$
\sqrt[{2 \sqrt{2 \sqrt[3]{2 \sqrt[4]{2 \sqrt[5]{2 \cdots}}}}}]{ }
$$-/
theorem algebra_611368 : ∏' (n : ℕ), (2 : ℝ) ^ (∏ i ∈ Finset.range (n 
  + 1), 1 / (i + 1 : ℝ)) = 2 ^ (Real.exp 1 - 1) := by
  -- Simplify (1 / 1 ⬝ 1 / 2 ⬝ ⋯ ⬝ 1 / n) as factorial.
  have hlm (n : ℕ) : (1 / (n + 1).factorial : ℝ) = ∏ i ∈ Finset.range (n 
  + 1), 1 / (i + 1 : ℝ) := by
    simp
    norm_cast
    rw [Finset.prod_range_add_one_eq_factorial]
  -- Substitute this into the expression.
  simp [<-hlm, -one_div]
  -- Show that 1 / n! has a sum, using the given theorem about taylor expression of Real.exp.
  have h₀ : HasSum (fun (n : ℕ) => (1 : ℝ) ^ n / n.factorial) (Real.exp 1) := by
    rw [Real.exp_eq_exp_ℝ]
    apply NormedSpace.expSeries_div_hasSum_exp
  -- Take log to change the infinite product to an infinite series, and use the above result to show that this infinite series has a sum.
  replace h₀ : HasSum (fun (n : ℕ) => Real.log ((2 : ℝ) ^ (1 / (n + 1).factorial : ℝ))) (Real.log (2 ^ (Real.exp 1 - 1))) := by
    have (n : ℕ) : Real.log ((2 : ℝ) ^ ((1 : ℝ) / (n + 1).factorial)) = Real.log 2 * (1 / (n + 1).factorial) := by
      rw [Real.log_rpow (by norm_num), mul_comm]
    simp [this, Real.log_rpow (show 0 < 2 by norm_num), -one_div]
    rw [mul_comm]
    apply HasSum.mul_left
    rw [@hasSum_nat_add_iff _ _ (Real.exp 1 - 1) _ _ (fun (n : ℕ) => (1 / n.factorial : ℝ)) 1]
    simp [-one_div] at h₀ ⊢
    exact h₀
  -- Verify that 0 < 2 ^ (1 / (n + 1)!).
  have h₁ (n : ℕ) : 0 < (2 : ℝ) ^ ((n + 1).factorial : ℝ)⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  -- Prove that the infinite product has a (finite) value.
  replace h₀ : HasProd (fun (n : ℕ) => (2 : ℝ) ^ (1 / (n + 1).factorial : ℝ)) (Real.exp (Real.log (2 ^ (Real.exp 1 - 1)))) := h₀.rexp.congr (by simp [Real.exp_log, h₁])
  convert HasProd.tprod_eq h₀ using 1
  rw [Real.exp_log]
  exact Real.rpow_pos_of_pos (by norm_num) _
