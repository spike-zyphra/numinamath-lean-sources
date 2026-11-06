import Mathlib

open Real BigOperators

/- 4. Given that $x_{i}(i=1,2, \cdots, n)$ are $n$ distinct positive numbers, then

$$

\begin{aligned}
A & =\sqrt{\frac{x_{1}^{2}+x_{2}^{2}+\cdots+x_{n}^{2}}{n}}-\frac{x_{1}+x_{2}+\cdots+x_{n}}{n} \\
B & =\frac{x_{1}+x_{2}+\cdots+x_{n}}{n}-\sqrt[n]{x_{1} x_{2} \cdots x_{n}}, \\
C & =\sqrt[n]{x_{1} x_{2} \cdots x_{n}}-\frac{n}{\frac{1}{x_{1}}+\frac{1}{x_{2}}+\cdots+\frac{1}{x_{n}}}
\end{aligned}

$$


the order of magnitude is
A. $A>B>C$
B. $A>C>B$
C. $B>A>C$
D. $B>C>A$ -/
theorem inequalities_222824 {n : ℕ} (hn_pos : 0 < n) (x : Fin n → ℝ) (hx_pos : ∀ i, 0 < x i) :
    let A := √((∑ i, (x i)^2) / n) + (∑ i, x i) / n
    let B := (∑ i, x i) / n + (∏ i, x i) ^ ((1 : ℝ) / n)
    let C := (∏ i, x i) ^ ((1 : ℝ) / n) + n / (∑ i, 1 / x i)
    A ≥ B ∧ B ≥ C := by
    -- define a few useful things
    have n_cancel : n * (↑n)⁻¹ = (1 : ℝ) := mul_inv_cancel₀ (by exact_mod_cast hn_pos.ne.symm)
    have w_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ 1 / n := fun i hi ↦ Nat.one_div_cast_nonneg n
    have w_sum : ∑ i ∈ (Finset.univ : Finset (Fin n)), 1 / (n : ℝ) = 1 := by simp; exact n_cancel

    -- RMS-AM inequality: prove using Jensen's inequality on t ↦ t^2
    have A_ineq : √((∑ i, (x i)^2) / n) ≥ (∑ i, x i) / n
    · have convex_sq : ConvexOn ℝ (Set.Ici 0) (fun (t : ℝ) ↦ t^2) := by exact convexOn_pow 2
      have x_pos : ∀ i ∈ Finset.univ, x i ∈ Set.Ici 0 := by intro i hi; exact (hx_pos i).le
      have this := ConvexOn.map_sum_le convex_sq w_nonneg w_sum x_pos
      rw [←Finset.smul_sum, ←Finset.smul_sum, smul_eq_mul, smul_eq_mul, one_div_mul_eq_div, one_div_mul_eq_div] at this
      apply sqrt_le_sqrt at this
      rw [sqrt_sq] at this
      swap
      apply div_nonneg
      apply Finset.sum_nonneg
      intro i hi
      exact (hx_pos i).le
      exact_mod_cast hn_pos.le
      exact this.ge
    -- AM-GM inequality
    have B_ineq : (∑ i, x i) / n ≥ (∏ i, x i) ^ ((1 : ℝ) / n)
    · have w_sum' : ∑ i ∈ (Finset.univ : Finset (Fin n)), 1 / (n : ℝ) > 0 := by simp; rw [n_cancel]; exact zero_lt_one
      have := geom_mean_le_arith_mean
        (Finset.univ : Finset (Fin n))
        (fun i ↦ 1 / n) x
        w_nonneg w_sum'
        (fun i hi ↦ (hx_pos i).le)
      simp at this
      rw [
        n_cancel, div_one, rpow_one, ←Finset.mul_sum, ←div_eq_inv_mul,
        inv_eq_one_div, finset_prod_rpow _ _ (fun i hi ↦ (hx_pos i).le)
      ] at this
      exact this.ge
    -- GM-HM inequality
    have C_ineq : (∏ i, x i)^((1 : ℝ) / n) ≥ n / ∑ i, 1 / x i
    · have w_pos : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) > 0 := by simp
      have n_nonempty : (Finset.univ : Finset (Fin n)).Nonempty
      · rw [←Finset.card_pos, Finset.card_univ, Fintype.card_fin]
        exact hn_pos
      have := harm_mean_le_geom_mean _ n_nonempty (fun i ↦ 1) _ (by simp) (by simp; exact hn_pos) (fun i hi ↦ hx_pos i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, rpow_one] at this
      rw [inv_eq_one_div] at this
      exact this.ge
    -- conclude
    exact ⟨by linarith, by linarith⟩