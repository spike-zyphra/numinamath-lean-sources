import Mathlib

open Real

/- Example 7 Let $a_{1}, a_{2}, \cdots, a_{n}(n>1)$ be real numbers, and $A+\sum_{i=1}^{n} a_{i}^{2}<\frac{1}{n-1}\left(\sum_{i=1}^{n} a_{i}\right)^{2}$, prove that: $A<2 a_{i} a_{j}(1 \leqslant i < j \leq slant n)$. -/
theorem inequalities_220738 {n : ℕ} (hn : n > 1) (a : Fin n → ℝ)
    (h : ∑ i : Fin n, (a i)^2 + A < 1 / (n - 1) * (∑ i : Fin n, a i)^2) :
    ∀ i j : Fin n, i < j → A < 2 * a i * a j := by
  intro i j hij
  have hi := Finset.mem_univ i
  have hj : j ∈ Finset.univ \ {i} := by simp; omega
  calc
    -- we have
    -- A < 1 / (n - 1) * (∑ i, a i) ^ 2 - ∑ i, a i ^ 2 from h
    A < 1 / (n - 1) * (∑ i, a i) ^ 2 - ∑ i, a i ^ 2 := lt_sub_left_of_add_lt h
    -- show that ∑ i, a i) ^ 2 ≤ (n - 1) * (∑ i, a i ^ 2 + 2 * a i * a j)
    _ ≤ 1 / (n - 1) * ((n - 1) * (∑ i, a i ^ 2 + 2 * a i * a j)) - ∑ i, a i ^ 2 := by
        apply sub_le_sub_right
        have hn0 : 0 < 1 / ((n : ℝ) - 1) := by
          rw [one_div_pos]
          rify at hn
          linarith
        rw [mul_le_mul_left hn0]
        -- we have
        -- (∑ k, a k) ^ 2 = (∑ k, ∑ k, (if k = j then 0 else 1) * (if k = i then a i + a j else if k = j then 0 else a k)) ^ 2
        calc
          (∑ k, a k) ^ 2 = (∑ k, (if k = j then 0 else 1) * (if k = i then a i + a j else if k = j then 0 else a k)) ^ 2 := by
              simp_rw [Finset.sum_eq_add_sum_diff_singleton hi]
              simp_rw [Finset.sum_eq_add_sum_diff_singleton hj]
              simp [show i ≠ j by omega, add_assoc]
              congr 3
              apply Finset.sum_congr rfl
              simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and, and_imp]
              intro k hki hkj
              simp [hki, hkj]
          -- apply the Cauchy-Schwarz inequality and get
          -- (∑ k, a k) ^ 2 ≤ (∑ k, (if k = j then 0 else 1) ^ 2) * (∑ k, (if k = i then a i + a j else if k = j then 0 else a k) ^ 2)
          _ ≤ (∑ k, (if k = j then 0 else 1) ^ 2) * (∑ k, (if k = i then a i + a j else if k = j then 0 else a k) ^ 2) := by
              apply Finset.sum_mul_sq_le_sq_mul_sq
          -- we have ∑ k, (if k = j then 0 else 1) ^ 2 = n - 1
          -- and ∑ k, (if k = i then a i + a j else if k = j then 0 else a k) ^ 2 = (∑ k, a k ^ 2) + 2 * a i * a j
          _ = (n - 1) * ((∑ k, a k ^ 2) + 2 * a i * a j) := by
              congr
              · rw [Finset.sum_eq_add_sum_diff_singleton (show j ∈ Finset.univ by simp)]
                rw [Finset.sum_eq_card_nsmul (b := 1) (by simp)]
                simp [Finset.card_univ_diff]
                push_cast [hn]
                rfl
              · simp_rw [Finset.sum_eq_add_sum_diff_singleton hi]
                simp_rw [Finset.sum_eq_add_sum_diff_singleton hj]
                simp only [show j ≠ i by omega, reduceIte]
                ring_nf
                congr 1
                apply Finset.sum_congr rfl
                simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
                  ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, and_imp]
                intro k hki hkj
                simp only [hki, ↓reduceIte, hkj]
    -- simplify the expression to get the final result
    -- A < 2 * a i * a j
    _ = 2 * a i * a j := by
        field_simp [show (n : ℝ) - 1 ≠ 0 by rify at hn; linarith]