import Mathlib

/-
Show that the sequence $ a_{1}, a_{2}, \ldots, a_{n} $ is super-increasing if $ a_{j+1} > 2 a_{j} $ for $ j=1,2, \ldots, n-1 $.
-/
theorem number_theory_4971
    (a : ℕ → ℕ)
    (h_a0 : a 0 > 0)
    (h : ∀ j, a (j + 1) > 2 * a j)
    : ∀ i, a i > (∑ j ∈ Finset.range i, a j) := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  cases k with
  | zero =>
    -- Base Case: a 0 > 0
    exact h_a0
  | succ k =>
    -- Inductive Step:
    have r1 : a (k + 1) > 2 * a k := h k
    -- relating the sum of the first $ k $ terms
    rw [Finset.sum_range_succ_comm a k]
    -- simplifying to a_k > \sum_{i=1}^{k-1} a_i
    apply (fun x => Nat.lt_trans x r1)
    rw [two_mul]
    apply Nat.add_lt_add_left
    exact ih k (lt_add_one k)
