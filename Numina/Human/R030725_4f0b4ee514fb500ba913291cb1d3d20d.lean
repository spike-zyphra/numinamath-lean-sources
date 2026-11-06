import Mathlib

/- auxiliary lemma for the sum of a geometric series -/
lemma l_sum_2pow (k : ℕ) : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
    induction k with
    | zero => simp
    | succ k ik =>
      rw [Finset.range_succ, Finset.sum_insert]
      rw [ik]
      rw [(Nat.add_sub_assoc Nat.one_le_two_pow (2 ^ (k + 1))).symm]
      rw [Nat.two_pow_succ (k + 1)]
      exact Finset.not_mem_range_self

/- definition of super_increasing -/
abbrev is_super_increasing1 (seq : ℕ → ℕ) : Prop :=
  ∀ i, seq i > (∑ j ∈ Finset.range i, seq j)

/-
Show that if $ a_{1}, a_{2}, \ldots, a_{n} $ is a super-increasing sequence, then $ a_{j} \geqslant 2^{j-1} $ for $ j=1,2, \ldots, n $.
-/
theorem number_theory_4970
    (a : ℕ → ℕ)
    (h_asi : is_super_increasing1 a)
    : ∀ j, (a j ≥ 2 ^ j) := by
  -- Since the subscript starts from 0,
  -- the bound is 2 ^ j instead of 2 ^ (j + 1)
  -- We will use induction to prove the statement.
  intro j
  induction' j using Nat.strong_induction_on with j ih

  cases j with
  | zero =>
    -- Base Case: For j = 0 (in LEAN the indice starts with zero)
    specialize h_asi 0
    norm_num at h_asi
    norm_num; linarith
  | succ j =>
    -- Inductive Step:

    have h_gt: a (j + 1) > ∑ i ∈ Finset.range (j + 1), a i := h_asi (j + 1)

    have h_sum_ge: ∑ i < j + 1, a i ≥ ∑ i < j + 1, 2 ^ i := by
      apply Finset.sum_le_sum
      simp; exact ih
    rw [Nat.Iio_eq_range] at h_sum_ge

    -- calculate the sum of a geometric series
    rw [l_sum_2pow j] at h_sum_ge

    exact Nat.le_of_pred_lt (Nat.lt_of_le_of_lt h_sum_ge h_gt)
