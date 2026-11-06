import Mathlib

open Real
open scoped BigOperators

/- 4. Given the quadratic trinomial $f(x)=a x^{2}+b x+c$ where all coefficients are positive and $a+b+c=1$, prove that for any set of positive numbers $x_{1}, x_{2}, \cdots, x_{n}$ satisfying $x_{1} x_{2} \cdots x_{n}=1$, we have $f\left(x_{1}\right) f\left(x_{2}\right) \cdots f\left(x_{n}\right) \geqslant 1$. -/
theorem inequalities_173340 {n : ℕ} (hn : 0 < n) (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1)
  (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hxprod : ∏ i, x i = 1) :
  ∏ i, (a * (x i)^2 + b * x i + c) ≥ 1 := by
  -- first we'll prove nonnegativity of all values, this will be useful later
  have hx' : ∀ i, 0 ≤ x i := by
    rintro i
    exact le_of_lt <| hx i
  calc
    -- we'll use 3 variable weighted am-gm on each term
    ∏ i, (a * x i ^ 2 + b * x i + c) ≥ ∏ i, ((x i ^ 2)^a * (x i)^b) := by
      rw [ge_iff_le]
      apply Finset.prod_le_prod
      all_goals rintro i hi
      . have := hx i
        positivity
      . convert Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ a by linarith) (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
          (show 0 ≤ (x i)^2 by positivity) (show 0 ≤ x i by linarith [hx i]) (show 0 ≤ 1 by norm_num) (by assumption) using 1
        all_goals simp
    -- next break the product into those with power a and those with power b
    _ = (∏ i, (x i ^ 2)^a) * (∏ i, (x i)^b) := by exact Finset.prod_mul_distrib
    -- take the powers out of individiual terms
    _ = ((∏ i, x i)^2)^a * (∏ i, x i)^b := by
      congr
      . rw [Real.finset_prod_rpow Finset.univ _ (by simp_rw [sq_nonneg]; simp)]
        rw [Finset.prod_pow]
      . exact Real.finset_prod_rpow Finset.univ x (by simp [hx']) b
    -- use the fact that products are 1 to prove target
    _ = 1 := by rw [hxprod]; simp