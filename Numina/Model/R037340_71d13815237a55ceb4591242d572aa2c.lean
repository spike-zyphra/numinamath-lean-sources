import Mathlib

-- This is used in both the following lemma and theorem.
lemma eq_icc : {n : ℕ | (1.2 : ℝ) * n - 4.4 < 5.2} = Set.Icc 0 7 := by
  ext n
  simp
  apply Iff.intro <;> intro h
  . -- Prove that n ≤ 7 if 1.2 * n - 4.4 < 5.2.
    suffices _ : n < 8 by
      omega
    rify
    calc
      n = (1.2 : ℝ) * n / 1.2 := by rw [mul_div_cancel_left₀]; norm_num
      _ = (1.2 * n - 4.4 + 4.4) / 1.2 := by norm_num
      _ < (5.2 + 4.4) / 1.2 := by apply div_lt_div_of_pos_right; linarith only [h]; norm_num
      _ = 8 := by norm_num
  . -- Prove that 1.2 * n - 4.4 < 5.2 if n ≤ 7.
    replace h : n < 8 := by
      omega
    rify at h
    rw [sub_lt_iff_lt_add', show (4.4 + 5.2 : ℝ) = 1.2 * 8 by norm_num]
    rw [mul_lt_mul_left]
    exact h
    norm_num

-- This is needed in the formalization of the theorem.
lemma finite_lemma : {n : ℕ | (1.2 : ℝ) * n - 4.4 < 5.2}.Finite := by
  rw [eq_icc]
  exact Set.finite_Icc 0 7

theorem algebra_12825 : ∑ k in finite_lemma.toFinset, k = 28 := by
  have h1 : finite_lemma.toFinset = {0, 1, 2, 3, 4, 5, 6, 7} := by
    ext n
    simp [eq_icc, finite_lemma, Set.mem_setOf_eq, Set.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    <;> omega
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]