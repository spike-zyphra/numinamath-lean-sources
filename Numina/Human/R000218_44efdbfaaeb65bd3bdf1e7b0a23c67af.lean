import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-The infinity sequence  $r_{0},r_{1},...$  of rational numbers it satisfies that: $\prod_{i=1}^ {k}r_{i}=\sum_{i=1}^{k} r_{i}$ .
For all natural k.
Show that  $\frac{1}{r_{n}}-\frac{3}{4}$  is a square of rationale number for all natural  $n\geq2$-/
theorem number_theory_8601
  (r : ℕ → ℚ) (h0 : ∀ k, r k ≠ 0)
  (SeqP : ∀ k, ∏ i in Finset.range (k + 1), r i = ∑ i in Finset.range (k + 1), r i) :
  ∀ n, 3 ≤ n → ∃ x:ℚ, x ^ 2 = 1 / r n - 3 / 4 := by
-- Rewrite assumptions and prepare some simple facts for later use
  intro n hn
  have h'n : 2 ≤ n - 1 := by
    rw [show 3=2+1 by norm_num, ← @Nat.sub_one_add_one n] at hn
    linarith; linarith
-- Denote the sum of all $r(i)$'s by $S(n)$ and prove a series of relations between $S$ and $r$
  let S : ℕ → ℚ := fun k => ∑ i in Finset.range (k + 1), r i
-- Split the sum and product by isolating the last term
  have t0 : ∀ k, 1 ≤ k → S (k - 1) * r k = S (k - 1) + r k := by
    intro k hk
    have q0 : S (k - 1) = ∑ i in Finset.range k, r i := by
      simp [S]; congr; rw [Nat.sub_one_add_one]; linarith
    have q'0 := SeqP (k-1)
    simp only [@Nat.sub_one_add_one k (show k≠0 by linarith)] at q'0
    have q1 := Finset.prod_range_succ r k
    have q2 := Finset.sum_range_succ r k
    have q3 := SeqP k
    rw [q1, q2, q'0, ← q0] at q3; assumption
-- Prove that when $k$ is greater or equal to $1$, $S(k)$ is not equal to $1$
  have t1 : ∀ k, 1 ≤ k → S k ≠ 1 := by
    intro k hk; by_contra h'
    have u1 : S (k-1) + r k = 1 := by
      symm; rw [← h']; simp [S]; rw [Finset.sum_range_succ r k]
      congr; rw [Nat.sub_one_add_one]; linarith
    have u2 : 4 * S (k-1) * r k ≤ 1 := by
      have : (S (k - 1) + r k) ^ 2 = 1 := by rw [u1]; simp
      rw [← this]; ring_nf; rw [show (4:ℚ)=2+2 by norm_num, mul_add, add_assoc]
      simp; rw [mul_comm, ← mul_assoc]; apply two_mul_le_add_sq
    have u3 : S (k-1) * r k = 1 := by
      simp [S]; simp [S] at h'; rw [← SeqP (k-1)]
      simp only [@Nat.sub_one_add_one k (show k≠0 by linarith)]
      rw [← Finset.prod_range_succ r k, SeqP k]; assumption
    rw [mul_assoc, u3] at u2; linarith
-- Prove that for any $k$, $S(k)$ is not zero
  have t'1 : ∀ k, S k ≠ 0 := by
    intro k hk
    have v0 := t0 (k+1)
    simp at v0; rw [hk] at v0; simp at v0
    have := h0 (k+1)
    symm at this; contradiction
-- Prove for $k$ greater or equal to 2, $r(k)$ can be expressed in terms of $S(k-1)$
  have t2 : ∀ k, 2 ≤ k → r k = S (k - 1) / (S (k - 1) - 1) := by
    intro k hk
    have h'k : 1 ≤ k - 1 := by
      rw [show 2=1+1 by norm_num, ← @Nat.sub_one_add_one k] at hk
      linarith; linarith
    have w0 := t0 k (show 1≤k by linarith)
    symm; rw [div_eq_iff, mul_sub, mul_one]
    rw [mul_comm, w0]; ring; by_contra h'
    rw [sub_eq_zero] at h'
    have := t1 (k-1) h'k
    contradiction
-- Prove for $k$ greater or equal to 2, $S(k)$ can be expressed in terms of $S(k-1)$
  have t3 : ∀ k, 2 ≤ k → S k = S (k - 1) ^ 2 / (S (k - 1) - 1) := by
    intro k hk
    have h'k : 1 ≤ k - 1 := by
      rw [show 2=1+1 by norm_num, ← @Nat.sub_one_add_one k] at hk
      linarith; linarith
    have h''k : S (k-1) - 1 ≠ 0 := by
      by_contra h'
      rw [sub_eq_zero] at h'
      have := t1 (k-1) h'k
      contradiction
    have o1 := t2 k hk
    have o2 : S k = S (k-1) + r k := by
      simp [S, @Nat.sub_one_add_one k (show k≠0 by linarith)]
      apply Finset.sum_range_succ
    symm at o1; rw [div_eq_iff] at o1
    symm; rw [div_eq_iff, o2, add_mul, ← o1]
    ring; assumption; assumption
-- Apply these relations to $n$ and $n-1$ and prove rewrite $1/r n- 3/4$ as a square
  have t5 := t2 n (show 2≤n by linarith)
  have t6 := t3 (n-1) h'n
  rw [Nat.sub_sub] at t6; simp at t6
  use 1/S (n-2)-1/2; rw [sub_pow_two, t5, mul_comm, ← mul_assoc]
  rw [show (1:ℚ)/2*2=1 by norm_num, one_mul, one_div_div, sub_div]
  rw [div_self, sub_sub]; nth_rw 2 [add_comm]; rw [← sub_sub]
  rw [show ((1:ℚ)/2)^2=1/4 by norm_num, show (1:ℚ)-3/4=1/4 by norm_num]
  rw [add_comm]; nth_rewrite 2 [sub_eq_add_neg]; rw [add_right_inj]
  rw [t6, one_div_div, ← neg_div, neg_sub, sub_div, div_pow]
  rw [one_pow, sub_right_inj, div_eq_div_iff]; ring
  exact t'1 (n-2); simp; push_neg; exact t'1 (n-2)
  exact t'1 (n-1)