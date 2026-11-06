import Mathlib

/-Let $A_n$ be the sum of the first $n$ terms of the geometric series
\[704 + \frac{704}{2} + \frac{704}{4} + \dotsb,\]and let $B_n$ be the sum of the first $n$ terms of the geometric series
\[1984 - \frac{1984}{2} + \frac{1984}{4} - \dotsb.\]Compute the value of $n \ge 1$ for which $A_n = B_n.$-/
theorem algebra_16678 {A B : ℕ → ℝ} (hn : 1 ≤ n )
(hA : A = fun n => ∑ i ∈ Finset.range n, 704 / 2 ^ i)
(hB : B = fun n => ∑ i ∈ Finset.range n, (-1) ^ i * 1984 / 2 ^ i) :
A n = B n ↔ n = 5 := by
-- Break "iff" and introduce the assumption
  constructor
  · intro h
-- Use geom_sum_eq to rewrite hA and hB as explicit formulas
    apply_fun (fun t => Function.eval n t) at hA hB; norm_num at hA hB
    have : ∑ i ∈ Finset.range n, (704:ℝ) / 2 ^ i = 704 * ∑ i ∈ Finset.range n, (1 / 2) ^ i := by
      rw [Finset.mul_sum, Finset.sum_congr]; rfl; intros; ring_nf
    rw [this, geom_sum_eq] at hA; ring_nf at hA
    replace this : ∑ i ∈ Finset.range n, (-1:ℝ) ^ i * 1984 / 2 ^ i = 1984 * ∑ i ∈ Finset.range n, (-1 / 2) ^ i := by
      rw [Finset.mul_sum, Finset.sum_congr]; rfl; intros; ring_nf; rw [← mul_pow]; ring
    rw [this, geom_sum_eq] at hB; ring_nf at hB
-- Rewrite h using hA and hB, then solve for $n$
    rw [hA, hB, div_pow, div_pow, one_pow] at h
    cases Nat.even_or_odd n
    · rw [Even.neg_one_pow] at h
      apply_fun (fun t => t + 1 / 2 ^ n * 1408 - 3968 / 3) at h; ring_nf at h
      suffices : ((1:ℝ) / 2) ^ n < 1 ;linarith
      apply pow_lt_one; any_goals linarith
      assumption
    rw [Odd.neg_one_pow] at h
    apply_fun (fun t => t + 1 / 2 ^ n * 1408 - 3968 / 3) at h; ring_nf at h
    apply_fun (fun t => 3 * t / 8192) at h; ring_nf at h; symm at h
    rw [show (1:ℝ)/32=(1/2)^5 by norm_num, pow_right_inj] at h; assumption
    any_goals norm_num; assumption
    any_goals norm_num
-- Conversely, check that when $n$ equals $5$, $A_n$ and $B_n$ are equal
  intro hn; rw [hA, hB, hn]; norm_num
