import Mathlib

open Nat Finset Real

/-
The Binomial Theorem states that for any variables \(x\) and \(y\) and a positive integer \(n\), the expression \((x+y)^{n}\) can be expanded as follows:
\[
(x+y)^{n} = \binom{n}{0} x^{n} + \binom{n}{1} x^{n-1} y + \binom{n}{2} x^{n-2} y^{2} + \cdots + \binom{n}{n-2} x^{2} y^{n-2} + \binom{n}{n-1} x y^{n-1} + \binom{n}{n} y^{n}
\]
Alternatively, this can be expressed using summation notation:
\[
(x+y)^{n} = \sum_{j=0}^{n} \binom{n}{j} x^{n-j} y^{j}
\]
We will prove the binomial theorem using mathematical induction.
-/
theorem number_theory_4681 {x y : ℝ} (n : ℕ) :
    (x + y) ^ n = ∑ j in range (n + 1), x ^ j * y ^ (n - j) * n.choose j := by
  have h : Commute x y := by dsimp [Commute,SemiconjBy]; ring
  -- Let t(n,m) = x^m * y^(n-m) * n.choose m.
  let t : ℕ → ℕ → ℝ := fun n m ↦ x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m ∈ range (n + 1), t n m
  -- First, we check $\forall n, t(n,0) = y^n$
  have h_first : ∀ n, t n 0 = y ^ n := fun n ↦ by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, tsub_zero]
  -- Second, we check $\forall n, t(n,n+1) = 0$
  have h_last : ∀ n, t n n.succ = 0 := fun n ↦ by
    simp only [t, choose_succ_self, cast_zero, mul_zero]
  -- Then, we check $\forall n, \forall i \in [0,n], t(n+1,i+1) = x*t(n,i) + y*t(n,i+1)$
  have h_middle :
      ∀ n i : ℕ, i ∈ range n.succ → (t n.succ i.succ) = x * t n i + y * t n i.succ := by
    intro n i h_mem
    have h_le : i ≤ n := le_of_lt_succ (mem_range.mp h_mem)
    dsimp only [t]
    rw [choose_succ_succ, cast_add, mul_add]
    congr 1
    · rw [pow_succ' x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, cast_zero, mul_zero, mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ' y, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  -- Now, we can do the induction.
  induction n with
  | zero =>
    -- In Base case, we have $(x + y) ^ 0 = ∑ m \in range (0 + 1), t(0,m)$.
    rw [pow_zero, sum_range_succ, range_zero, sum_empty, zero_add]
    -- Thus, the goal is reduced to $1 = t (0,0)$.
    dsimp only [t]
    -- That is $1 = x^0 * y^0 * 1$, which is true.
    rw [pow_zero, pow_zero, choose_self, cast_one, mul_one, mul_one]
  | succ n ih =>
    -- In Induction step.
    -- The goal can be reduce to $∑ i \in range (n + 1), x * t(n,i) + ∑ i \in range (n + 1), y * t(n,i) =∑ z \in range (n+1), x * t(n,z) + (∑ x \in range (n+1), y*t(n,x+1) + y^{n + 1})$
    rw [sum_range_succ', h_first, sum_congr rfl (h_middle n), sum_add_distrib, add_assoc,
      pow_succ' (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    -- That is $∑ i ∈ range (n + 1), y * t(n,i) = ∑ x ∈ range (n+1), y * t(n,x+1) + y^{n + 1}$
    -- which is true.
    rw [sum_range_succ', sum_range_succ, h_first, h_last, mul_zero, add_zero, _root_.pow_succ']
