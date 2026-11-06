import Mathlib

open Real Set
open scoped BigOperators

/- The domain of the function $f(x) = \arcsin(\log_{m}(nx))$ is a closed interval of length $\frac{1}{2013}$ , where $m$ and $n$ are positive integers and $m>1$. Find the remainder when the smallest possible sum $m+n$ is divided by 1000. -/
theorem algebra_95564 {k : ℕ} :
  IsLeast {k | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m > 1 ∧ k = m + n ∧
    (MeasureTheory.volume {x | 0 < (n: ℝ) * x ∧ -1 ≤ logb m (n * x) ∧ logb m (n * x) ≤ 1}).toReal = 1 / 2013} k
    → k % 1000 = 371 := by
    intro h_least
    -- The question asks for the value modulo 1000 of the minimum value of k, but we can calculate the minimum value of k explicitly
    suffices: IsLeast {k | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m > 1 ∧ k = m + n ∧
    (MeasureTheory.volume {x | 0 < (n: ℝ) * x ∧ -1 ≤ logb m (n * x) ∧ logb m (n * x) ≤ 1}).toReal = 1 / 2013} 5371
    rw [show k = 5371 from (IsLeast.isLeast_iff_eq h_least).mp this]
    -- We show that the domain is exactly the interval [1/mn, m/n]
    have h_dom: ∀ m n, (1 < m) → (0 < n) → {x | 0 < n * x ∧ -1 ≤ logb m (n * x) ∧ logb m (n * x) ≤ 1} = Set.Icc (1/((m: Real) * n)) ((m : Real) / n) := by
      intro m n hm hn
      ext x
      simp only [mem_setOf_eq, mem_Icc]
      -- We apply the definition of logarithms: -1 = log_m 1/m
      rw [show -1 = logb m m⁻¹ from by
        simp only [logb_inv, neg_inj, logb_self_eq_one hm]
      ]
      -- If x is in the interval [1/mn, m/n], then nx is positive. To avoid duplicating our work,
      -- we show that under the assumption that nx is positive, we have that x is in the domain
      -- if and only if x in in the interval [1/mn, m/n]
      have h_lemma: (0 < n * x) →
        (logb m m⁻¹ ≤ logb m (n * x) ∧ logb m (n * x) ≤ 1 ↔ 1/(m * n) ≤ x ∧ x ≤ m / n) := by
        intro h_nx
        -- log_m is increasing
        rw [logb_le_logb hm]
        -- We apply the definition of logarithms: 1 = log_m m
        nth_rewrite 1 [show 1 = logb m m from Eq.symm $ logb_self_eq_one hm]
        rw [logb_le_logb hm]
        nth_rewrite 1 [show m⁻¹ = n * (1/(m * n))  from by field_simp]
        rw [mul_le_mul_iff_of_pos_left hn]
        nth_rewrite 2 [show m = n * (m / n) from by field_simp]
        rw [mul_le_mul_iff_of_pos_left hn]
        all_goals positivity
      constructor
      intro ⟨h_nx, h_rhs⟩
      exact(h_lemma h_nx).mp h_rhs
      intro h_lhs
      -- We show that if x is in the interval [1/mn, m/n] then nx is positive
      have: 0 < x := by
        have: 1/m * (1/n) ≤ x := by
          field_simp
          exact h_lhs.left
        have: 0 < 1/m := by positivity
        have: 0 < 1/n := by positivity
        nlinarith
      have h_nx: 0 < n * x := by nlinarith
      exact ⟨h_nx, (h_lemma h_nx).mpr h_lhs⟩
    -- To show that 5371 is the smallest possible value of k, we show that it is a possible value for k
    -- and that it is a lower bound for the possible values of k
    rw [IsLeast.eq_1]
    -- We try m = 3. This gives an integral value of n: 5368
    constructor
    simp
    use 3
    and_intros
    norm_num
    use 5368
    and_intros
    norm_num; norm_num; norm_num
    rw [h_dom, volume_Icc]
    all_goals norm_num
    rw [lowerBounds.eq_1]
    simp only [gt_iff_lt, one_div, exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
    intro k m hm n hn hm_one h_sum h_vol
    -- The domain is the interval [1/mn, m/n], which has length m/n - 1/mn
    rw [h_dom, volume_Icc] at h_vol
    replace h_vol: (m : ℝ)/n - (1: ℝ) / (m * n) = (1: ℝ) / 2013 := by
      rw [one_div 2013, ← h_vol, ENNReal.toReal_ofReal]
      -- The length of an interval is an extended nonnegative real number, so we must show that
      -- that the real number that we claim that it is equal to is nonnegative
      have h_msq: ((m : ℝ)/n - (1: ℝ) / (m * n)) * (m * n) ≥ 0 := by
        rw [sub_mul, div_mul_comm, mul_div_assoc, div_self, mul_one, div_mul_comm, div_self, mul_one]
        rify at hm_one
        nlinarith
        all_goals positivity
      exact nonneg_of_mul_nonneg_left h_msq (by positivity)
    -- We solve for n in terms of m
    replace h_vol: n = 2013 * ((m: ℝ) - (1: ℝ)/m) := by
      rw [show n = 2013 * n * ((1:ℝ) / 2013) from by field_simp]
      rw [← h_vol, mul_assoc, mul_sub, ← mul_div_assoc, mul_comm (n: ℝ), mul_div_assoc, div_self, mul_one]
      rw [← mul_div_assoc, mul_one, mul_comm (m: ℝ), ← div_div, div_self]
      all_goals positivity
    -- A larger value of m will result in a larger value of n
    by_cases h_mbound: m ≥ 3
    rify at *
    have: (1: ℝ)/m ≤ 1/3 := (one_div_le_one_div hm (by norm_num)).mpr h_mbound
    have: m + n ≥ (5371: ℝ) := by linarith
    rwa [h_sum]
    -- The problem states that n > 1. Thus we try m = 2
    have h_meq: m = 2 := by linarith
    rw [h_meq] at h_vol
    -- We get 2n = 3 * 2013, and so n is not an integer
    have: 2 * n = 6039 := by
      rify
      rw [h_vol]
      norm_num
    omega
    all_goals (rify at *) ; assumption