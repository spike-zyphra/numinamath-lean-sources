import Mathlib

/-Given that $m$ and $n$ are both non-zero real numbers, if the solution set of $mx+n \gt 0$ is $x>\frac{2}{5}$, then the solution set of $nx-m \lt 0$ is ______.-/
theorem algebra_9372 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
(h : ∀ x, m * x + n > 0 ↔ 2 / 5 < x) :
∀ x, n * x - m < 0 ↔ -5 / 2 < x := by
-- Introduce a variable
  intro x
-- Plug in $x=-n/m$ to h and prove that $-n/m$ is less or equal to $2/5$
  have hmn := h (-n/m); rw [← mul_div_assoc, mul_div_cancel_left₀] at hmn
  simp at hmn
-- Plug in $x=0$ to h and prove that $n$ is negative
  have hn0 := h 0; simp at hn0
  rw [show ((2:ℝ)/5<0)=false by norm_num] at hn0; simp at hn0
  replace hn0 : n < 0 := by
    by_contra h'; push_neg at h'
    have : n=0 := by linarith
    contradiction
-- Plug in $x=1$ to h and prove that $m$ is positive
  have hm0 := h 1; simp at hm0
  rw [show ((2:ℝ)/5<1)=true by norm_num] at hm0; simp at hm0
  rw [← neg_lt_iff_pos_add] at hm0
  replace hm0 : 0 < m := by linarith
-- Plug in $x=2/5$ to h and prove that $-n/m$ is greater or equal to $2/5$
  have h'mn := h (2/5); simp at h'mn
  rw [← le_sub_iff_add_le] at h'mn; simp at h'mn
  rw [← le_div_iff₀'] at h'mn
-- Therefore $-n/m$ must be equal to $2/5$
  have mdn : - n / m = 2 / 5 := by linarith
  rw [neg_div, neg_eq_iff_eq_neg, ← inv_inj] at mdn
  rw [inv_neg, inv_div, inv_div] at mdn
-- Rewrite the final goal and prove it 
  simp; rw [← div_lt_iff_of_neg', mdn, ← neg_div]
  assumption; assumption; assumption