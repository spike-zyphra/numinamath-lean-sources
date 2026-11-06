import Mathlib
set_option maxRecDepth 5000

open Finset

/- Die reellen Zahlen $r_{1}, r_{2}, \ldots, r_{2019}$ erfüllen die Bedingungen
$r_{1}+r_{2}+\ldots+r_{2019}=0$ (1) sowie $r_{1}^{2}+r_{2}^{2}+\ldots+r_{2019}^{2}=1$ (2).
Es sei $a=\min \left(r_{1}, r_{2}, \ldots, r_{2019}\right)$ und $b=\max \left(r_{1}, r_{2}, \ldots, r_{2019}\right)$. Man beweise: $a b \leq \frac{-1}{2019}$. -/
theorem inequalities_605266 {r : ℕ → ℝ} (hsum : ∑ i ∈ range 2019, r i = 0)
(hsumsq : ∑ i ∈ range 2019, r i ^ 2 = 1) :
let a := (image r (range 2019)).min' (by use r 0; simp; use 0; simp);
let b := (image r (range 2019)).max' (by use r 0; simp; use 0; simp); a * b ≤ -1 / 2019 := by
-- Introduce assumptions, prove that $b$ is greater or equal to any $r_i$ and $a$ is less or equal to any $r_i$
  intro a b; have bmax : ∀ i ∈ range 2019, r i ≤ b := by
    intro i hi; apply le_max'; simp; use i; simp at *; exact hi
  have amin : ∀ i ∈ range 2019, a ≤ r i  := by
    intro i hi; apply min'_le; simp; use i; simp at *; exact hi
-- Prove that $b$ is positive and $a$ is negative by contradiction
  have bpos : 0 < b := by
    by_contra!; rw [sum_eq_zero_iff_of_nonpos] at hsum
    rw [sum_congr rfl (show ∀ i ∈ range 2019, r i ^ 2 = 0 by intros; simp; apply hsum; assumption)] at hsumsq
    simp at hsumsq; intros; apply le_trans _ this; apply bmax; assumption
  have aneg : a < 0 := by
    by_contra!; rw [sum_eq_zero_iff_of_nonneg] at hsum
    rw [sum_congr rfl (show ∀ i ∈ range 2019, r i ^ 2 = 0 by intros; simp; apply hsum; assumption)] at hsumsq
    simp at hsumsq; intros; apply le_trans this; apply amin; assumption
-- Denote $P$ to be the set of indexes of positive terms and $N$ to be the set of indexes of nonpositive terms
  let P := {i ∈ range 2019| 0 < r i}; let N := {i ∈ range 2019| r i ≤ 0}
-- Prove $P$ and $N$ are disjoint
  have PNdisj : Disjoint P N := by simp [disjoint_iff, Finset.ext_iff, P, N]; intros; assumption
-- Prove that $P$ unions $N$ is the whole set $range 2019$
  have PUN : P ∪ N = range 2019 := by
    simp [Finset.ext_iff, P, N]; intro i; simp [← and_or_left]
    intro; exact lt_or_le 0 (r i)
-- Prove the sum of cardinalities of $P$ and $N$ is $2019$
  have addC := PUN; apply_fun fun t => t.card at addC
  simp [card_union_of_disjoint PNdisj] at addC
-- Split the sums in hsum and hsumsq according to this partition
  rw [← PUN, sum_union PNdisj, ← eq_neg_iff_add_eq_zero, ← sum_neg_distrib] at hsum
  rw [← PUN, sum_union PNdisj] at hsumsq
-- Estimate the two sums in hsumsq using bmax and amin
  have sumsqP : ∑ x ∈ P, r x ^ 2 ≤ -#N * (a * b) := by calc
    _ ≤ ∑ x ∈ P, b * r x := by
      apply sum_le_sum; intro i hi; rw [pow_two, mul_le_mul_right]
      apply bmax; apply mem_of_subset _ hi; apply filter_subset
      simp [P] at hi; exact hi.right
    _ = b * ∑ x ∈ N, -r x := by rw [← mul_sum, hsum]
    _ ≤ b * ∑ x ∈ N, -a := by
      rw [mul_le_mul_left]; apply sum_le_sum; intro i hi; simp
      apply amin; apply mem_of_subset _ hi; apply filter_subset; exact bpos
    _ = _ := by simp; ring
  have sumsqN : ∑ x ∈ N, r x ^ 2 ≤ -#P * (a * b) := by calc
    _ ≤ ∑ x ∈ N, a * r x := by
      apply sum_le_sum; intro i hi; rw [pow_two]; apply mul_le_mul_of_nonpos_right
      apply amin; apply mem_of_subset _ hi; apply filter_subset
      simp [N] at hi; exact hi.right
    _ = -a * ∑ x ∈ N, -r x := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ -a * ∑ x ∈ P, b := by
      rw [mul_le_mul_left, ← hsum]; apply sum_le_sum; intro i hi
      apply bmax; apply mem_of_subset _ hi; apply filter_subset
      simp; exact aneg
    _ = _ := by simp; ring
-- Put together what we have proved so far and use linarith to finish the final goal
  rify at addC; rw [le_div_iff₀, ← addC]; linarith; simp