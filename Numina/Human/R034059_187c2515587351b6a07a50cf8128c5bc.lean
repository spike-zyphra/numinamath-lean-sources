import Mathlib


/-- What is $$\sum_{i=1}^{100} \sum_{j=1}^{100} i + j? -/
theorem algebra_98341 : ∑ i in Finset.Icc 1 100, ∑ j in Finset.Icc 1 100, (i + j) = 1010000 := by
  -- The gaussian sum formula states that $\sum_{i=1}^n i = (n+1)n/2$.
  have (n : ℕ) (h : 0 < n) : ∑ i ∈ Finset.Icc 1 n, i = (n + 1) * n / 2 := by
    convert Finset.sum_range_id (n+1) using 1
    have : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      cases k with
      | zero => simp[h]
      | succ k => simp[Nat.succ_le]
    rw[← Finset.sum_insert_zero (a := 0), this]
    rfl
  -- Now consider the inner sum $\sum_{j=1}^n i + j =\sum_{j=1}^n i + \sum_{j=1}^n j = n * i + (n+1)n/2$.
  conv => lhs; rhs; intro i; rw[Finset.sum_add_distrib (f := fun x => i) (g := fun j => j), Finset.sum_const]
  simp only [Nat.card_Icc, Nat.reduceAdd, Nat.add_one_sub_one, smul_eq_mul]
  rw[Finset.sum_add_distrib, ← Finset.mul_sum]
  -- This shows that $\sum_{i=1}^n\sum_{j=1}^n i + j = \sum_{i=1}^n n * i + (n+1)n/2.
  conv => lhs; rhs; rhs; intro i; rw[this _ (by simp)]
  -- But this equals n * (n+1)n/2 + n * (n+1)n/2 = n^2 (n+1), once for the constant term, once for the sum over i.
  conv => lhs; rhs; rw[Finset.sum_const]
  rw[this _ (by simp)]
  simp only [Nat.card_Icc, Nat.add_one_sub_one, smul_eq_mul]
  -- Choose n = 100, this shows the sum equals 1010000.
  change 100 * 5050 + 100 * 5050 = 1010000
  simp