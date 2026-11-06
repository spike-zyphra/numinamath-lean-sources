import Mathlib

/- The sequence of real numbers $a_{0}, a_{1}, a_{2}, \ldots$ is defined recursively by  $$ a_{0}=-1, \quad \sum_{k=0}^{n} \frac{a_{n-k}}{k+1}=0 \quad \text { for } \quad n \geq 1 $$  Show that $a_{n}>0$ for $n \geq 1$.  (Poland) -/
theorem algebra_23530 {a : ℕ → ℝ}
    (ha0 : a 0 = -1)
    (han : ∀ n ≥ 1, ∑ k in Finset.range (n + 1), a (n - k) / (k + 1) = 0) :
    ∀ n ≥ 1, a n > 0 := by
    intro n hn
    -- $a_{n+1} = \frac{1}{n+2} \sum_{k=1}^{n} \frac{k}{(n-k+1)(n-k+2)} a_{k}$ for $n \geq 1$.
    have h1 : ∀ n ≥ 1, a (n + 1) = 1 / (n + 2) * ∑ k ∈ Finset.Icc 1 n, k / ((n - k + 1) * (n - k + 2)) * a k := by
      clear n hn
      intro n hn
      -- Show $$ \sum_{k=0}^{n} \frac{a_{k}}{n-k+1}=0 $$.
      have h1 := han n (by linarith)
      have : ∑ k ∈ Finset.range (n + 1), a (n - k) / ((k : ℝ) + 1) =
        ∑ k ∈ Finset.range (n + 1), a (n - k) / (n - ↑(n - k) + 1) := by
        congr! with k hk
        simp at hk
        rw [Nat.cast_sub]
        simp
        linarith
      rw [this, Finset.sum_flip (n := n) (fun k => a k / (n - k + 1))] at h1
      -- $$ \sum_{k=0}^{n+1} \frac{a_{k}}{n-k+2}=0 $$
      have h2 := han (n + 1) (by linarith)
      have : ∑ k ∈ Finset.range (n + 1 + 1), a (n + 1 - k) / ((k : ℝ) + 1) =
        ∑ k ∈ Finset.range (n + 1 + 1), a (n + 1 - k) / (n - ↑(n + 1 - k) + 2) := by
        congr! 2 with k hk
        simp at hk
        rw [Nat.cast_sub]
        simp
        linarith
        omega
      rw [this, Finset.sum_flip (n := n + 1) (fun k => a k / (n - k + 2))] at h2
      -- 0=(n+2) \sum_{k=0}^{n+1} & \frac{a_{k}}{n-k+2}-(n+1) \sum_{k=0}^{n} \frac{a_{k}}{n-k+1}
      have h3 : (n + 2) * ∑ k ∈ Finset.range (n + 1 + 1), a k / (↑n - ↑k + 2) -
        (n + 1) * ∑ k ∈ Finset.range (n + 1), a k / (↑n - ↑k + 1) = 0 := by
        simp [h1, h2]
      -- (n+2) a_{n+1}+\sum_{k=0}^{n}\left(\frac{n+2}{n-k+2}-\frac{n+1}{n-k+1}\right) a_{k} = 0
      have h4 : (n + 2) * a (n + 1) + ∑ k ∈ Finset.range (n + 1),
          ((n + 2) / (n - k + 2) - (n + 1) / (n - k + 1) ) * a k = 0 := by
        rw [Finset.sum_range_succ, mul_add, add_comm, ← add_sub] at h3
        rw [← h3]
        congr 1
        · simp; left
          norm_num
        · simp [Finset.mul_sum, sub_mul, ← Finset.sum_sub_distrib, mul_comm, mul_sub, mul_div, mul_comm]
      rw [← eq_neg_iff_add_eq_zero, mul_comm, ← eq_div_iff (by linarith)] at h4
      rw [h4, mul_comm, mul_one_div, Finset.sum_range_eq_add_Ico _ (by linarith)]
      simp [div_self (a := (n : ℝ) + 2) (by linarith), div_self (a := (n : ℝ) + 1) (by linarith),
        ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr (by rfl) ?_
      intro k hk
      rw [← neg_mul]
      congr
      simp at hk ⊢
      rw [← mul_div_mul_right _ _ (c := (n : ℝ) - k + 2) (by rw [← Nat.cast_sub (by linarith)]; positivity),
        ← mul_div_mul_left _ (b := (n : ℝ) - k + 2) (c := (n : ℝ) - k + 1)
        (by rw [← Nat.cast_sub (by linarith)]; positivity), ← sub_div]
      congr
      ring
    rw [show n = (n - 1) + 1 by omega]
    apply Nat.strong_induction_on (p := fun n => a (n + 1) > 0) (n - 1)
    intro n hn
    -- if $n = 0$, then $a_{1} = > 0$.
    by_cases hn' : n = 0
    · simp [hn']
      specialize han 1 (by linarith)
      rw [Finset.sum_range_succ] at han
      simp [ha0] at han
      linarith
    -- The coefficients of $a_{1}, \ldots, a_{n}$ are all positive. Therefore, $a_{1}, \ldots, a_{n}&gt;0$ implies $a_{n+1}&gt;0$.
    · rw [h1 n (by omega)]
      apply mul_pos (by positivity)
      apply Finset.sum_pos _ (by simp; omega)
      intro k hk
      obtain  ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      apply mul_pos
      · apply div_pos (by simp; omega)
        apply mul_pos
        <;> norm_cast <;> omega
      · rw [show k = k - 1 + 1 by omega]
        specialize hn (k - 1) (by omega)
        exact hn