import Mathlib
/- Sindy writes down the positive integers less than 200 in increasing order, but skips the multiples of 10. She then alternately places + and - signs before each of the integers, yielding an expression $+1-2+3-4+5-6+7-8+9-11+12-\cdots-199$. What is the value of the resulting expression? -/
theorem number_theory_609310 : ∑ i in Finset.range 10, (∑ j in Finset.range 9, (-1) ^ j * (20 * (↑i : ℝ) + 1 + ↑j) + ∑ k in Finset.range 9, (-1) ^ (k + 1) * (20 * (↑i : ℝ) + 11 + ↑k)) = -100:= by
  -- First, we prove that for each i in range 10, the inner sum equals -10
  have h1 : ∀ i ∈ Finset.range 10, (∑ j in Finset.range 9, (-1) ^ j * (20 * (↑i : ℝ) + 1 + ↑j) + ∑ k in Finset.range 9, (-1) ^ (k + 1) * (20 * (↑i : ℝ) + 11 + ↑k)) = -10:= by
    intro i _
    repeat rw [Finset.sum_range_succ]
    simp
    norm_num
    ring_nf
  -- Using h1, we rewrite the original sum as the sum of -10 repeated 10 times
  have h2 : ∑ i in Finset.range 10, (∑ j in Finset.range 9, (-1) ^ j * (20 * (↑i : ℝ) + 1 + ↑j) + ∑ k in Finset.range 9, (-1) ^ (k + 1) * (20 * (↑i : ℝ) + 11 + ↑k)) = ∑ i in Finset.range 10, -10:= by exact Finset.sum_congr rfl h1
  -- Apply h2 and simplify to get the final result
  rw [h2]
  simp
  linarith
