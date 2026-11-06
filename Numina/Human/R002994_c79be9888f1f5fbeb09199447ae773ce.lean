import Mathlib

open Real

/- 4.3.6 $\star \star$ Let $a_{1}, a_{2}, \cdots, a_{n}, b_{1}, b_{2}, \cdots, b_{n}$ be positive real numbers, and satisfy $\sum_{k=1}^{n} a_{k}=\sum_{k=1}^{n} b_{k}$. Prove:

$$

\sum_{k=1}^{n} \frac{a_{k}^{2}}{a_{k}+b_{k}} \geqslant \frac{1}{2} \sum_{k=1}^{n} a_{k} .

$$
 -/
theorem inequalities_140880 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ k, a k = ∑ k, b k) :
    ∑ k, (a k)^2 / (a k + b k) ≥ 1 / 2 * ∑ k, a k := by

      -- use ≤ instead of ≥
      simp only [ge_iff_le]

      -- a_i + b_i is non-negative
      have f_nonneg : ∀ (i : Fin n), 0 ≤ a i + b i := by
        intro i
        have := ha i
        have := hb i
        positivity

      -- and a_i ^ 2 / (a_i + b_i)
      have g_nonneg : ∀ (i : Fin n), 0 ≤ a i ^ 2 / (a i + b i) := by
        intro i
        have := ha i
        have := hb i
        positivity

      -- so we apply cauchy to a_i + b_i and a_i ^ 2 / (a_i + b_i)
      have cauchy := Real.sum_sqrt_mul_sqrt_le
        (f := fun i => a i + b i)
        (g := fun i => a i ^ 2 / (a i + b i))
        Finset.univ f_nonneg g_nonneg

      -- we can simplify terms in the LHS of cauchy's inequality because
      -- √(a i + b i) * √(a i ^ 2 / (a i + b i)) = a i
      have terms_eq : ∀ i, √(a i + b i) * √(a i ^ 2 / (a i + b i)) = a i := by
        intro i
        -- a_i and b_i are positive
        have := ha i
        have := hb i
        -- cancel fraction
        rw [←Real.sqrt_mul (f_nonneg i), mul_div, mul_div_cancel_left₀]

        -- √x ^ 2 = x
        exact sqrt_sq (by positivity)

        -- we used that a i + b i is not zero
        positivity

      simp_rw [terms_eq] at cauchy

      -- we can also simplify further using
      -- ∑ (a i + b i) = 2 * ∑ a i
      have sum_f : ∑ i : Fin n, (a i + b i) = 2 * ∑ i : Fin n, a i := by
        rw [Finset.sum_add_distrib, hsum]
        ring

      rw [sum_f] at cauchy

      -- the sum of a values is positive
      have sum_pos : 0 < ∑ i : Fin n, a i := by
        apply Finset.sum_pos
        · norm_num
          exact ha
        refine Finset.univ_nonempty_iff.mpr ?_
        exact Fin.pos_iff_nonempty.mp hn

      rw [←Real.sqrt_mul (by positivity)] at cauchy

      -- The sum of over a_i ^ 2 / (a_i + b_i) is non-negative
      have : 0 ≤ ∑ i : Fin n, (a i ^ 2 / (a i + b i)) := by
        apply Finset.sum_nonneg
        norm_num
        exact g_nonneg

      -- we separate ∑ a_i ^ 2 / (a_i + b_i) on the RHS
      rw [Real.le_sqrt (by positivity) (by positivity), ←div_le_iff₀' (by positivity)] at cauchy

      -- then we have our inequality
      convert cauchy using 1
      · field_simp
        ring