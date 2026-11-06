import Mathlib

open Real

/- Let $n$ be an integer and $\left(a_{1}, \cdots, a_{n}\right)$ be positive real numbers whose product is 1. Show that $\prod_{i=1}^{n}\left(2+a_{i}\right) \geq 3^{n}$. -/
theorem inequalities_142479 (n : ℕ) (a : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∏ i, a i = 1) :
    ∏ i, (2 + a i) ≥ 3 ^ n := calc
  -- show that 2 + a i ≥ 3 * a i ^ (1 / 3)
  ∏ i, (2 + a i) ≥ ∏ i, 3 * a i ^ (1 / 3 : ℝ) := by
    apply Finset.prod_le_prod
    · intro i _
      apply mul_nonneg (by norm_num)
      apply Real.rpow_nonneg
      exact le_of_lt (h₀ i)
    · intro i _
      have h1 : 0 ≤ (1 : ℝ) := by norm_num
      have h3 : 0 ≤ (1 / 3 : ℝ) := by norm_num
      -- we have the following AM-GM inequality:
      -- (1 * 1 * a i)^(1 / 3) ≤ (1 + 1 + a i) / 3
      -- which is equivalent to
      -- 3 * a i ^ (1 / 3) ≤ 2 + a i
      have ineq := Real.geom_mean_le_arith_mean3_weighted h3 h3 h3 h1 h1 (le_of_lt (h₀ i)) (by norm_num)
      rw [one_rpow] at ineq
      linarith
  -- the result follows from the assumption that ∏ i, a i = 1
  _ = (∏ i : Fin n, 3) * (∏ i, a i) ^ (1 / 3 : ℝ) := by
    rw [Finset.prod_mul_distrib, Real.finset_prod_rpow]
    intro i _
    exact le_of_lt (h₀ i)
  _ ≥ 3 ^ n := by rw [h₁, one_rpow, mul_one, Fin.prod_const]