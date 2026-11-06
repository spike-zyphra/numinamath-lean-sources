import Mathlib

namespace inequalities_603033

lemma induction_downward (n : ℕ) {P : ℕ → Prop} :
  P n → (∀ k ∈ Finset.Icc 0 (n - 1), P (k + 1) → P k) → ∀ k ∈ Finset.Icc 0 n, P k := by
  simp only [Finset.mem_Icc, zero_le, true_and]
  intro hn h k hk
  induction hk using Nat.decreasingInduction with
  | of_succ k h' ih =>
    exact h _ (Nat.le_sub_one_of_lt h') ih
  | self =>
    exact hn

/-For $ k = 1, 2, \cdots, n -1 $, by induction, we have : 
$$\sum^{k}_{i=1} i(a_{k-1} - 2 a_k + a_{k+1}) = a_0 - (k + 1) a_k + k a_{k+1} $$ -/
lemma sum_Icc_weighted_second_differences (k : ℕ) (a : ℕ → ℝ) :
  ∑ i ∈ Finset.Icc 1 k, i * (a (i - 1) - 2 * a i + a (i + 1)) =
    a 0 - (k + 1) * a k + k * a (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by simp)]
    rw [ih]
    rw [show k + 1 - 1 = k by rfl]
    push_cast
    ring

end inequalities_603033

open inequalities_603033

/-
8-155 Let real numbers $a_{0}, a_{1}, \cdots, a_{n}$ satisfy
$$a_{0}=a_{n}=0, a_{k-1}-2 a_{k}+a_{k+1} \geqslant 0, k=1,2, \cdots, n-1 .$$
Prove: $a_{k} \leqslant 0, k=0,1,2, \cdots, n$.-/
theorem inequalities_603033 (n : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 0) (han : a n = 0)
    (h : ∀ k ∈ Finset.Icc 1 (n - 1), a (k - 1) - 2 * a k + a (k + 1) ≥ 0) :
    ∀ k ∈ Finset.Icc 0 n, a k ≤ 0 := by
  -- Since $(a_{k-1} - 2 a_k + a_{k+1}) \ge 0$, $a_0 - (k + 1) a_k + ka_{k+1} \ge 0$
  have h1 : ∀ k ∈ Finset.Icc 1 (n - 1), a 0 - (k + 1) * a k + k * a (k + 1) ≥ 0 := by
    intro k hk
    have h2 : ∀ i ∈ Finset.Icc 1 k, i * (a (i - 1) - 2 * a i + a (i + 1)) ≥ 0 := by
      intro i hi
      simp_all
      apply mul_nonneg
      · simp
      · apply h
        <;> nlinarith
    have h3 : ∑ i ∈ Finset.Icc 1 k, i * (a (i - 1) - 2 * a i + a (i + 1)) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i hi
      exact h2 i hi
    -- For $ k = 1, 2, \cdots, n -1 $, by induction, we have : 
    -- $$\sum^{k}_{i=1} i(a_{k-1} - 2 a_k + a_{k+1}) = a_0 - (k + 1) a_k + k a_{k+1} $$
    have h4 : ∑ i ∈ Finset.Icc 1 k, i * (a (i - 1) - 2 * a i + a (i + 1)) =
      a 0 - (k + 1) * a k + k * a (k + 1) := sum_Icc_weighted_second_differences k a
    rw [h4] at h3
    exact h3
  -- By $a_0 = 0$,  
  -- $ (k+1)a_{k} \le ka_{k+1} $
  rw [ha0] at h1
  -- By downward-induction, it suffices to show $a_n \le 0$ and $a_{k+1} \le 0 \Rightarrow a_{k} \le 0$.
  apply induction_downward
  · rw [han]
  · intro k hk
    intro hak
    by_cases hk1 : k ≥ 1
    · simp_all only [Finset.mem_Icc, ge_iff_le, and_imp, zero_sub, le_neg_add_iff_add_le, add_zero,
      zero_le, true_and]
      --  It follows from the above inequality
      have := h1 k hk1 hk
      nlinarith [this]
    · simp only [ge_iff_le, not_le, Nat.lt_one_iff] at hk1
      rw [hk1, ha0]

