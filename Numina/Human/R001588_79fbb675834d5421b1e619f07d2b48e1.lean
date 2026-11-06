import Mathlib

/- 47. (ROM 6) Prove the inequality $x_{1} x_{2} \cdots x_{k}\left(x_{1}^{n-1}+x_{2}^{n-1}+\cdots+x_{k}^{n-1}\right) \leq x_{1}^{n+k-1}+x_{2}^{n+k-1}+\cdots+x_{k}^{n+k-1}$, where $x_{i}>0(i=1,2, \ldots, k), k \in N, n \in N$. -/
theorem other_24713 {k : ℕ} {n : ℕ} (x : Fin k → ℝ) (hxp : ∀ i, 0 < x i) (np : 0 < n) :
    (∏ i, x i) * (∑ i, (x i) ^ (n - 1)) ≤ ∑ i, (x i) ^ (n + k - 1) := by
  by_cases h₀ : k = 0
  . -- The case k = 0 is trivial and is considered first.
    subst h₀
    simp
  . replace h₀ : 1 ≤ k := by
      omega
    replace np : 1 ≤ n := by
      omega
    have h₁ : 0 < n + k - 1 := by
      omega
    -- We prove a lemma first, according to the solution.
    have lm (j : Fin k) : (∏ i : Fin k, x i) * x j ^ (n - 1) ≤ (((∑ i, (x i) ^ (n + k - 1)) + (n - 1) * x j ^ (n + k - 1)) / (n + k - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_fin_eq_sum_range, Finset.prod_fin_eq_prod_range, show Finset.range k = Finset.range k \ {j.val} ∪ {j.val} by simp, Finset.sum_union (by simp), Finset.prod_union (by simp)]
      rw [mul_assoc, add_assoc]
      simp [-Finset.sum_sdiff_eq_sub]
      rw [show (x j ^ (n + k - 1) + (n - 1) * x j ^ (n + k - 1)) = n * x j ^ (n + k - 1) by ring]
      nth_rewrite 1 [show x j = x j ^ 1 by simp]
      rw [<-pow_add, Nat.add_comm, Nat.sub_add_cancel np]
      -- First simplify the left-hand side of the inequality.
      have h₂ : (∏ m ∈ Finset.range k \ {↑j}, if h : m < k then x ⟨m, h⟩ else 1) * x j ^ n = (∏ m ∈ Finset.range k, (if h : m < k then x ⟨m, h⟩ ^ (n + k - 1) else 0) ^ (if m = j then (n / (n + k - 1 : ℕ) : ℝ) else (1 / (n + k - 1 : ℕ) : ℝ))) := by
        nth_rewrite 2 [show Finset.range k = Finset.range k \ {j.val} ∪ {j.val} by simp]
        rw [Finset.prod_union (by simp)]
        simp [-one_div]
        congrm ?_ * ?_
        . rw [Finset.prod_congr]
          . rfl
          . intro m hm
            simp at hm
            simp [hm.1, hm.2]
            rw [Real.pow_rpow_inv_natCast]
            exact le_of_lt (hxp ⟨m, hm.1⟩)
            linarith only [h₁]
        . rw [<-Real.rpow_natCast, <-Real.rpow_natCast, <-Real.rpow_mul (le_of_lt (hxp j))]
          congrm ?_ ^ ?_
          . rfl
          . symm
            rw [<-mul_div_assoc]
            apply div_eq_of_eq_mul (by norm_cast; linarith only [h₁])
            rw [mul_comm]
      -- Then simplify the right-hand side of the inequality.
      have h₃ : (((∑ m ∈ Finset.range k \ {↑j}, if h : m < k then x ⟨m, h⟩ ^ (n + k - 1) else 0) + n * x j ^ (n + k - 1)) / (n + k - 1 : ℕ) : ℝ) = (∑ m ∈ Finset.range k, (if m = j then (n / (n + k - 1 : ℕ) : ℝ) else (1 / (n + k - 1 : ℕ) : ℝ)) * (if h : m < k then x ⟨m, h⟩ ^ (n + k - 1) else 0)) := by
        nth_rewrite 2 [show Finset.range k = Finset.range k \ {j.val} ∪ {j.val} by simp]
        rw [Finset.sum_union (by simp)]
        simp [-one_div, -Finset.sum_sdiff_eq_sub]
        rw [add_div, Finset.sum_div]
        congrm ?_ + ?_
        . rw [Finset.sum_congr]
          . rfl
          . intro m hm
            simp at hm
            simp [hm.1, hm.2, -one_div]
            rw [div_eq_mul_one_div, mul_comm]
        . apply div_eq_of_eq_mul (by norm_cast; linarith only [h₁])
          rw [div_mul_comm]
          nth_rewrite 3 [mul_comm]
          rw [<-mul_div_assoc]
          rw [div_mul_cancel₀ _ (by norm_cast; linarith only [h₁])]
      rw [h₂, h₃]
      -- Apply the weighted AM-GM inequality.
      apply Real.geom_mean_le_arith_mean_weighted (Finset.range k)
      intro m hm
      positivity
      rw [show Finset.range k = Finset.range k \ {j.val} ∪ {j.val} by simp, Finset.sum_union (by simp)]
      simp [-one_div, -Finset.sum_sdiff_eq_sub]
      have h₄ : (∑ m ∈ Finset.range k \ {↑j}, if m = j then (n / (n + k - 1 : ℕ) : ℝ) else (1 / (n + k - 1 : ℕ) : ℝ)) = ∑ m ∈ Finset.range k \ {↑j}, (1 / (n + k - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_congr rfl]
        intro m hm
        simp at hm
        simp [hm.2, -one_div]
      replace h₄ : (∑ m ∈ Finset.range k \ {↑j}, if m = j then (n / (n + k - 1 : ℕ) : ℝ) else (1 / (n + k - 1 : ℕ) : ℝ)) = ((k - 1) / (n + k - 1 : ℕ) : ℝ) := by
        rw [h₄]
        rw [Finset.sum_const, Finset.card_sdiff (by simp)]
        simp [-one_div]
        rw [<-div_eq_mul_one_div]
        norm_cast
      rw [h₄, <-add_div, div_eq_of_eq_mul (by norm_cast; linarith only [h₁])]
      norm_cast
      omega
      intro m hm
      simp at hm
      simp [hm]
      apply pow_nonneg (le_of_lt (hxp ⟨m, hm⟩))
    -- Add k inequalities together, each of them is a direct application of the previous lemma.
    have h₂: ∑ j, ((∏ i, x i) * (x j) ^ (n - 1)) ≤ ∑ j, (((∑ i, (x i) ^ (n + k - 1)) + (n - 1) * (x j) ^ (n + k - 1)) / (n + k - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact lm j
    -- Do simplifications.
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range] at h₂ ⊢
    have h₃ : ∑ i ∈ Finset.range k, (if h : i < k then (∑ i : Fin k, x i ^ (n + k - 1) + (↑n - 1) * x ⟨i, h⟩ ^ (n + k - 1)) / ↑(n + k - 1) else 0) = ∑ i ∈ Finset.range k, (((if h : i < k then ∑ i : Fin k, x i ^ (n + k - 1) else 0) + (if h : i < k then (n - 1) * x ⟨i, h⟩ ^ (n + k - 1) else 0))/ (n + k - 1: ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl]
      intro i hi
      simp at hi
      simp [hi]
    have h₄ : (∑ i ∈ Finset.range k, if h : i < k then (∏ i : Fin k, x i) * x ⟨i, h⟩ ^ (n - 1) else 0) = (∑ i ∈ Finset.range k, (∏ i : Fin k, x i) * if h : i < k then x ⟨i, h⟩ ^ (n - 1) else 0) := by
      rw [Finset.sum_congr rfl]
      intro i hi
      simp at hi
      simp [hi]
    rw [h₃, <-Finset.sum_div, Finset.sum_add_distrib] at h₂
    rw [Finset.mul_sum, <-h₄]
    have h₅ : (∑ i ∈ Finset.range k, if h : i < k then ∑ i : Fin k, x i ^ (n + k - 1) else 0) = (∑ i ∈ Finset.range k, ∑ i : Fin k, x i ^ (n + k - 1)) := by
      rw [Finset.sum_congr rfl]
      intro i hi
      simp at hi
      simp [hi]
    replace h₅ : (∑ i ∈ Finset.range k, if h : i < k then ∑ i : Fin k, x i ^ (n + k - 1) else 0) = k * ∑ i, x i ^ (n + k - 1) := by
      rw [h₅, Finset.sum_const, Finset.card_range]
      simp
    have h₆ : (∑ i ∈ Finset.range k, if h : i < k then (n - 1) * x ⟨i, h⟩ ^ (n + k - 1) else 0) = ∑ i, (n - 1) * x i ^ (n + k - 1) := by
      rw [Finset.sum_fin_eq_sum_range]
    rw [<-Finset.mul_sum] at h₆
    rw [h₅, h₆, <-add_mul, mul_comm] at h₂
    norm_cast at h₂
    rw [show k + (n - 1) = n + k - 1 by omega, mul_div_cancel_right₀, Finset.sum_fin_eq_sum_range] at h₂
    clear h₃ h₄ h₅ h₆
    exact h₂
    norm_cast
    linarith only [h₁]