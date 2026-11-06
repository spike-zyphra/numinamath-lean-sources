import Mathlib

/- 4. Let $a, b, c>0$ such that $a+b+c=1$. Show that if if $x_{1}, x_{2}, \ldots, x_{5}$ are positive real numbers such that $x_{1} x_{2} \ldots x_{5}=1$, then

$$

\left(a x_{1}^{2}+b x_{1}+c\right)\left(a x_{2}^{2}+b x_{2}+c\right) \cdots\left(a x_{5}^{2}+b x_{5}+c\right) \geq 1 .

$$
 -/
theorem inequalities_288022 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i)
    (hxp : ∏ i, x i = 1) :
    ∏ i, (a * x i ^ 2 + b * x i + c) ≥ 1 := by
  -- first prove all x(i) are nonnegative as that'll be used later
  have hx' : ∀ i, 0 ≤ x i := by
    rintro i
    exact le_of_lt <| hx i
  calc
    -- first use 3 var weighted am-gm on each of the terms, this also requires proving each term of  rhs is nonegative
    ∏ i, (a * x i ^ 2 + b * x i + c) ≥ ∏ i, ((x i ^ 2)^a * (x i)^b) := by
      rw [ge_iff_le]
      apply Finset.prod_le_prod
      all_goals rintro i hi
      . have := hx i
        positivity
      . convert Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ a by linarith) (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
          (show 0 ≤ (x i)^2 by positivity) (show 0 ≤ x i by linarith [hx i]) (show 0 ≤ 1 by norm_num) (by assumption) using 1
        all_goals simp
    -- next break the product into those with pwoer a and those with power b
    _ = (∏ i, (x i ^ 2)^a) * (∏ i, (x i)^b) := by exact Finset.prod_mul_distrib
    -- take the powers out of individiual terms
    _ = ((∏ i, x i)^2)^a * (∏ i, x i)^b := by
      congr
      . rw [Real.finset_prod_rpow Finset.univ _ (by simp_rw [sq_nonneg]; simp)]
        rw [Finset.prod_pow]
      . exact Real.finset_prod_rpow Finset.univ x (by simp [hx']) b
    -- use the fact that products are 1 to prove target
    _ = 1 := by rw [hxp]; simp