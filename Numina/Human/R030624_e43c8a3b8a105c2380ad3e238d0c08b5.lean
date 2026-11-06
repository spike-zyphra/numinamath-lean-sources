import Mathlib

/- What is the largest integer $n$ such that  $$(1 + 2 + 3 + \cdots+ n)^2 < 1^3 + 2^3 + \cdots+ 7^3?$$ -/
theorem algebra_19337 : IsGreatest {n : ℕ | (∑ i in Finset.Icc 1 n, i) ^ 2 < ∑ i in Finset.Icc 1 7, i ^ 3} 6 := by
  -- First we prove that $1^3 + 2^3 + 3^3 +\ldots + n^3 < 1^3 + 2^3 + 3^3 +\ldots + 7^3$ if and only if $n \leq 6$
  have main (n : ℕ) : (∑ i in Finset.Icc 1 n, i) ^ 2 < ∑ i in Finset.Icc 1 7, i ^ 3 ↔ n ≤ 6 := by
    -- $2 * (1 + 2 + 3 + \ldots + n) = n * (n + 1)$
    have eq1 (m : ℕ) : 2 * (∑ i in Finset.Icc 1 m, i) = m * (m + 1) := by
      induction' m with m hm
      simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero, zero_add, mul_one]
      rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 m), mul_add, hm]
      ring
    -- $(1 + 2 + 3 + \ldots + n)^2 = 1^3 + 2^3 + 3^3 +\ldots + n^3.$
    have eq2 (m : ℕ) : (∑ i in Finset.Icc 1 m, i) ^ 2 = ∑ i in Finset.Icc 1 m, i ^ 3 := by
      induction' m with m hm
      simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 m), Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 m), ← hm, add_sq, eq1]
      ring
    rw [eq2]
    -- $1^3 + 2^3 + 3^3 +\ldots + n^3$ is strictly increasing with respect to $n$
    have lt (b : ℕ) : ∀ a, a < b → ∑ i in Finset.Icc 1 a, i ^ 3 < ∑ i in Finset.Icc 1 b, i ^ 3 := by
      -- We prove this by induction on $b$
      induction' b with b hb
      -- Base case $b = 0$ is trivial
      simp only [not_lt_zero', zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, imp_self, implies_true]
      -- If $\forall a < b, 1^3 + 2^3 + 3^3 +\ldots + a^3 < 1^3 + 2^3 + 3^3 +\ldots + b^3$, then $\forall a < b + 1, 1^3 + 2^3 + 3^3 +\ldots + a^3 < 1^3 + 2^3 + 3^3 +\ldots + (b + 1)^3$
      intro a hab
      -- if $1 \leq a$
      if ha : 1 ≤ a then
        have aeq : a = a - 1 + 1 := by
          rw [Nat.sub_add_cancel ha]
        have ale : a - 1 < b := by
          linarith
        rw [aeq, Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 (a - 1)), Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 b)]
        have le1 := hb (a - 1) ale
        have le2 : (a - 1 + 1) ^3 < (b + 1) ^ 3 := by
          rw [← aeq]
          apply pow_lt_pow_left
          exact hab
          exact Nat.zero_le a
          exact Ne.symm (Nat.zero_ne_add_one 2)
        linarith
      -- else $a = 0$
      else 
        simp only [not_le, Nat.lt_one_iff] at ha
        rw [ha]
        rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 1 b)]
        simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_pos_iff, or_true, pow_pos]
    constructor
    · -- If $1^3 + 2^3 + 3^3 +\ldots + n^3 < 1^3 + 2^3 + 3^3 +\ldots + 7^3$ then $n \leq 6$
      intro h
      by_contra contra
      -- If $n = 7$
      if hn1 : n = 7 then
        rw [hn1] at h
        linarith
      -- Else $7 < n$
      else 
        have ngt : 7 < n := by
          have nge : 7 ≤ n := by
            apply Nat.succ_le_of_lt
            exact Nat.gt_of_not_le contra
          exact Nat.lt_of_le_of_ne nge fun a => hn1 (id (Eq.symm a))
        have := lt n 7 ngt
        linarith
    · -- If $n \leq 6$ then $1^3 + 2^3 + 3^3 +\ldots + n^3 < 1^3 + 2^3 + 3^3 +\ldots + 7^3$
      intro hn1
      have nlt : n < 7 := by 
        exact Nat.lt_add_one_of_le hn1
      exact lt 7 n nlt
  -- Now we prove the main theorem
  constructor
  exact (main 6).mpr (by norm_num) 
  intro n hn
  exact (main n).mp hn