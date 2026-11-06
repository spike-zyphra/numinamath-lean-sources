import Mathlib

/-The sum of the first 5 terms of an arithmetic series is $70$.  The sum of the first 10 terms of this  arithmetic series is $210$.  What is the first term of the series?-/
theorem algebra_21421 {a d : ℝ} (h₀ : ∑ i ∈ Finset.range 5, (a + d * i) = 70)
    (h₁ : ∑ i ∈ Finset.range 10, (a + d * i) = 210) :
    a = 42 / 5 := by
  -- show that the sum of the first n terms of an arithmetic series
  have sum₁ (n : ℕ) : ∑ i ∈ Finset.range n, (a + d * i) = n * a + n * (n - 1) / 2 * d := by
    -- induction on n
    induction n with
    | zero => simp -- base case
    | succ n hn => -- inductive step
      rw [Finset.sum_range_succ]
      rw [hn]
      rify
      ring_nf
  -- show that 5a + 10d = 70 and 10a + 45d = 210
  rw [sum₁ 5] at h₀
  rw [sum₁ 10] at h₁
  rify at h₀ h₁
  norm_num at h₀ h₁
  -- show that 2d = 14 - a and 9d = 42 - 2a
  replace h₀ : 2 * d = 14 - a := by linarith only [h₀]
  replace h₁ : 9 * d = 42 - 2 * a := by linarith only [h₁]
  -- show that 126 - 9a = 84 - 4a
  have eq : 126 - 9 * a = 84 - 4 * a := by linarith only [h₀, h₁]
  -- show that a = 42 / 5
  linarith only [eq]
