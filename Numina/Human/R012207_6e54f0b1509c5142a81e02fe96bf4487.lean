import Mathlib
open Real
/- 4. Let $\left\{a_{n}\right\}$ be an arithmetic sequence with common difference $d(d \neq 0)$, and the sum of the first $n$ terms be $S_{n}$. If the sequence $\left\{\sqrt{8 S_{n}+2 n}\right\}$ is also an arithmetic sequence with common difference $d$, then the general term of the sequence $\left\{a_{n}\right\}$ is $a_{n}=$ $\qquad$ -/
theorem algebra_190032 {a : ℕ → ℝ} {d : ℝ} (h : ∀ n, a n = a 0 + d * n) (hpos : ∀ n, 8 * ∑ i ∈ Finset.range n, a i + 2 * n ≥ 0)
    (hd : d > 0) (hs : ∀ n, Real.sqrt (8 * ∑ i ∈ Finset.range n, a i + 2 * n) = d * n) :
    ∀ n, a n = 4 * n + 7 / 4 := by
  -- find alternative recurrence for a n
  have h₁ : ∀ n, 8 * a n + 2 = 2 * √(8 * ∑ i ∈ Finset.range n, a i + 2 * ↑n) * d + d ^ 2
  · intro n
    have := hs (n + 1)
    rw [Nat.cast_add, mul_add d, ←hs n, Nat.cast_one, mul_one,
        Real.sqrt_eq_iff_eq_sq, add_sq, Real.sq_sqrt (hpos n), Finset.sum_range_succ, mul_add] at this
    linarith [this]
    exact_mod_cast hpos (n + 1)
    positivity
  -- substitute in the original recurrence
  conv at h₁ =>
    intro n
    congr
    · rw [h n]
    · rw [hs n]
  -- find d
  have d_val : d = 4
  · have hd := h₁ 0
    have hd' := h₁ 1
    simp at hd hd'
    nlinarith [hd, hd']
  -- find a 0
  have a0_val : a 0 = 7 / 4
  · have := h₁ 1
    rw [d_val] at this
    linarith [this]
  -- conclude
  intro n
  rw [h, d_val, a0_val, add_comm]