import Mathlib

/- An aside: the sum of all the unit fractions

It is possible to show that, given any real M , there exists a positive integer $k$ large enough that:

$$
\sum_{n=1}^{k} \frac{1}{n}=\frac{1}{1}+\frac{1}{2}+\frac{1}{3} \ldots>M
$$

Note that this statement means that the infinite harmonic series, $\sum_{n=1}^{\infty} \frac{1}{n}$, grows without bound, or diverges.
For the specific example $\mathrm{M}=5$, find a value of $k$, not necessarily the smallest, such that the inequality holds. Justify your answer. -/
theorem number_theory_608457{M:ℝ}(hM: M = 5):
  ∃ k:ℕ, ∑ i ∈ Finset.range k, ((1:ℝ)/(1+i)) > M := by
  -- the statement is obviously true because harmonic series diverge.
  -- we can always find such k. here we choose 256, there are also other possible values.
  use 256
  -- note that 1/(n+1) + 1/(n+2) +... + 1/(n+n) >
  -- 1/(2n) + 1/(2n) + .. + 1/(2n) = 1/2.
  -- for convenience, here we only prove "≥" relation.
  have h1{n:ℕ}(hn: n ≠ 0): ∑ i ∈ Finset.range n, ((1:ℝ) / (1+ (n+i))) ≥ 1/2 := by
    have: (1/2:ℝ) = ∑ i ∈ Finset.range n, (1:ℝ) / (2*n) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    replace hn: 0 < n := Nat.zero_lt_of_ne_zero hn
    rw [this]
    apply Finset.sum_le_sum
    intro i
    simp only [Finset.mem_range]
    intro hi
    replace hi: i ≤ n-1 := Nat.le_sub_one_of_lt hi
    rify at hi
    apply (one_div_le_one_div (by simp [hn]) ?_).mpr ?_
    · norm_cast; simp
    · rw [Nat.cast_sub (by exact hn)] at hi
      simp only [Nat.cast_one] at hi
      linarith [hi]
  -- take n = 8,16,32,64,128.
  -- then we reduce the problem to prove 1+1/2+...+1/8 > 5/2.
  suffices ∑ i ∈ Finset.range 8, ((1:ℝ) / (1+i)) > 5/2 by
    have h2: 256 = 128 + 128 := by norm_num
    have h3: 128 = 64 + 64 := by norm_num
    have h4: 64 = 32 + 32 := by norm_num
    have h5: 32 = 16 + 16 := by norm_num
    have h6: 16 = 8 + 8 := by norm_num
    rw [h2, Finset.sum_range_add, h3, Finset.sum_range_add,
    h4, Finset.sum_range_add, h5, Finset.sum_range_add,
    h6, Finset.sum_range_add, ← h6, ← h5, ← h4, ← h3, hM]
    simp only [add_assoc]
    -- sum from 8 + sum from 16 + sum from 32 + sum from 64 + sum from 128
    -- ≥ 1/2 + 1/2 + 1/2 + 1/2 + 1/2 = 5/2.
    have h7{a1 a2 a3 a4 a5: ℝ}(ha1: a1 ≥ 1/2)(ha2: a2 ≥ 1/2)(ha3: a3 ≥ 1/2)
      (ha4: a4 ≥ 1/2)(ha5: a5 ≥ 1/2):
      a1 + (a2 + (a3 + (a4 + a5))) ≥ 5/2 := by
      linarith [ha1, ha2, ha3, ha4, ha5]
    replace h7: ∑ i ∈ Finset.range 8, ((1:ℝ) / (1 + (8+i))) +
      (∑ i ∈ Finset.range 16, ((1:ℝ) / (1 + (16+i))) +
      (∑ i ∈ Finset.range 32, ((1:ℝ) / (1 + (32+i))) +
      (∑ i ∈ Finset.range 64, ((1:ℝ) / (1 + (64+i))) +
      (∑ i ∈ Finset.range 128, ((1:ℝ) / (1 + (128+i))))))) ≥ 5/2 := by
      apply h7
      all_goals apply h1 (by norm_num)
    have h8{a1 a2: ℝ}(ha1: a1 > 5/2)(ha2: a2 ≥ 5/2): a1 + a2 > 5 := by
      linarith [ha1, ha2]
    apply h8 this ?_
    push_cast; exact h7
  -- now the goal turns to prove 1+ 1/2 + 1/3 + 1/4 +... + 1/8 > 5/2.
  -- use 1/(n+1) + ... + 1/(2n) ≥ 1/2 again.
  have h2': 8 = 4+4 := by norm_num
  rw [h2', Finset.sum_range_add]
  have h2: ∑ i ∈ Finset.range 4, (1:ℝ) / (1 + (4+i)) ≥ 1/2 := by
    apply h1 (by norm_num)
  -- then it suffices to show 1 + 1/2 + 1/3 + 1/4 > 2, which obviously follows.
  have h3: ∑ i ∈ Finset.range 4, (1:ℝ) / (1+i) > 2 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  -- done.
  linarith [h2, h3]