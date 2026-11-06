import Mathlib

open Real
open scoped BigOperators

/- $4-$ Prove the inequality: $\left(\frac{b_{1}+\ldots+b_{n}}{a_{1}+\ldots+a_{n}}\right)^{b_{1}+\ldots+b_{n}} \leq\left(\frac{b_{1}}{a_{1}}\right)^{b_{1}} \ldots\left(\frac{b_{n}}{a_{n}}\right)^{b_{n}}$.

The values of the variables are considered positive. -/
theorem inequalities_170500 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
  ((∑ i, b i) / (∑ i, a i)) ^ (∑ i, b i) ≤
  ∏ i, ((b i) / (a i)) ^ (b i) := by
    -- we have a non-zero amount of variables
    have fin_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn

    -- we will apply AM-GM using the weights
    -- b_i / (b_1 + .. + b_n)
    -- and the values a_i / b_i

    -- the sum of a values is positive
    have sum_a_pos : 0 < ∑ i, a i := by
      apply Finset.sum_pos
      · norm_num [ha]
      · exact Finset.univ_nonempty_iff.mpr fin_nonempty

    -- the sum of b values is positive
    have sum_b_pos : 0 < ∑ i, b i := by
      apply Finset.sum_pos
      · norm_num [hb]
      · exact Finset.univ_nonempty_iff.mpr fin_nonempty

    -- the weights are non-negative
    have weights_pos : ∀ i ∈ Finset.univ, 0 ≤ b i / ∑ i : Fin n, b i := by
      norm_num
      intro i
      have b_pos : 0 < b i := hb i
      positivity

    -- the weights sum to 1
    have weights_sum : ∑ i : Fin n, (fun i => b i / ∑ i : Fin n, b i) i = 1 := by
      norm_num
      convert_to (∑ x : Fin n, b x) / (∑ i : Fin n, b i) = 1
      · rw [Finset.sum_div]
      field_simp

    -- the values are non-negative
    have term_nonneg : ∀ i ∈ Finset.univ, 0 ≤ (fun i => a i / b i) i := by
      norm_num
      intro i
      have a_pos : 0 < a i := ha i
      have b_pos : 0 < b i := hb i
      positivity

    -- so we can apply AM-GM using the weights
    -- b_i / (b_1 + .. + b_n)
    -- and the values a_i / b_i
    have am_gm := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun i => b i / (∑ i, b i)) (fun i => a i / b i)
      weights_pos weights_sum term_nonneg

    -- simplify
    norm_num at am_gm

    -- we can simplify the RHS to (∑ k, a k) / (∑ i, b i)
    have rhs_eq : ∑ x, (b x / ∑ i, b i) * (a x / b x)
      = (∑ k, a k) / (∑ i, b i) := by
      trans ∑ k, (a k / ∑ i, b i)
      · congr
        ext k
        have b_pos : 0 < b k := hb k
        field_simp
        ring

      rw [Finset.sum_div]

    rw [rhs_eq] at am_gm

    -- the RHS is positive
    have rhs_pos : 0 < (∑ k, a k) / (∑ i, b i) := by positivity

    -- the LHS is positive
    have lhs_pos : 0 < ∏ x : Fin n, (a x / b x) ^ (b x / ∑ i : Fin n, b i) := by
      apply Finset.prod_pos
      norm_num
      intro i
      have a_pos : 0 < a i := ha i
      have b_pos : 0 < b i := hb i
      positivity

    -- so we can invert both sides and flip the inequality
    replace am_gm := (inv_le_inv₀ rhs_pos lhs_pos).mpr am_gm

    -- simplify
    norm_num at am_gm

    -- inverse distributes over product
    rw [←Finset.prod_inv_distrib] at am_gm

    -- we can simplify the RHS to
    -- ∏ x, ((b x / a x) ^ (b x / ∑ i, b i))
    have rhs_eq : ∏ x, ((a x / b x) ^ (b x / ∑ i, b i))⁻¹
      = ∏ x, ((b x / a x) ^ (b x / ∑ i, b i)) := by
        congr
        ext k
        rw [←inv_rpow]
        norm_num
        · have a_pos : 0 < a k := ha k
          have b_pos : 0 < b k := hb k
          positivity
    rw [rhs_eq] at am_gm

    -- we take the power of (∑ i, b i) on both sides
    have powed : ((∑ i, b i) / ∑ k, a k) ^ (∑ i, b i)
      ≤ (∏ x, (b x / a x) ^ (b x / ∑ i, b i)) ^ (∑ i, b i)
        := Real.rpow_le_rpow (by positivity) am_gm (by positivity)

    -- then we essentially have our wanted inequality
    convert powed
    -- we have to prove equality on the RHS
    -- power distributes over product
    · rw [←Real.finset_prod_rpow]
      -- then we prove that products are equal term-wise
      congr
      ext k
      -- a_k and b_k are positive
      have a_pos : 0 < a k := ha k
      have b_pos : 0 < b k := hb k

      -- merge powers
      rw [←Real.rpow_mul (by positivity)]

      -- simplify
      field_simp
      -- we used positivity of terms
      · norm_num
        intro k
        have a_pos : 0 < a k := ha k
        have b_pos : 0 < b k := hb k
        positivity