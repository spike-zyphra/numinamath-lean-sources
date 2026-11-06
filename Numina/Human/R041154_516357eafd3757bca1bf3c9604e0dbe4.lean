import Mathlib

open Finset Real

/- 12. Given real numbers $x_{1}, x_{2}, \cdots, x_{n}(n>2)$ satisfying $\left|\sum_{i=1}^{n} x_{i}\right|>1,\left|x_{i}\right| \leqslant 1(i=1,2, \cdots, n)$, prove that there exists a positive integer $k$, such that $\left|\sum_{i=1}^{k} x_{i}-\sum_{i=k+1}^{n} x_{i}\right| \leqslant 1$.
(2005 China Western Mathematical Olympiad) -/
theorem algebra_269137 {n : ℕ} (hn : n > 2) (x : ℕ → ℝ)
    (hsum : |∑ i ∈ Icc 1 n, x i| > 1) (hxi : ∀ i ∈ Icc 1 n, |x i| ≤ 1) :
    ∃ k > 0, k < n ∧ |∑ i ∈ Icc 1 k, x i - ∑ i ∈ Icc (k + 1) n, x i| ≤ 1 := by
  -- We prove by contradiction.
  by_contra! H
  -- Set g(k) := ∑ i ∈ Icc 1 k, x i - ∑ i ∈ Icc (k + 1) n, x i.
  let g (k : ℕ) := ∑ i ∈ Icc 1 k, x i - ∑ i ∈ Icc (k + 1) n, x i
  -- We have |g(0)| > 1, |g(n)| > 1 and g(0) + g(n) = 0.
  have hg0 : |g 0| > 1 := by
    simp [g, hsum]
  have hgn : |g n| > 1 := by
    simp [g, hsum]
  have hg0n : g 0 + g n = 0 := by
    simp [g]
  -- By hypothesis, we have |g(k)| > 1 for all k ≤ n.
  have hgk : ∀ k ≤ n, |g k| > 1 := by
    intro k hk
    obtain rfl | rfl | hk : k = 0 ∨ k = n ∨ 0 < k ∧ k < n := by omega
    . exact hg0
    . exact hgn
    . exact H k hk.1 hk.2
  -- But we have |g(k + 1) - g(k)| ≤ 2 for all k < n.
  have hgdiff : ∀ k < n, |g (k + 1) - g k| ≤ 2 := by
    intro k hk
    -- g(k + 1) - g(k) = 2 * x(k + 1)
    suffices g (k + 1) - g k = 2 * x (k + 1) by
      simp [this, abs_mul]
      exact hxi (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simp [g]
    suffices ∑ i ∈ Icc 1 (k + 1), x i - ∑ i ∈ Icc 1 k, x i = x (k + 1) ∧ ∑ i ∈ Icc (k + 1) n, x i - ∑ i ∈ Icc (k + 1 + 1) n, x i = x (k + 1) by
      linarith only [this]
    constructor
    . simp [Finset.sum_Icc_succ_top]
    . have : Icc (k + 1) n = {k + 1} ∪ Icc (k + 1 + 1) n := by
        ext i
        simp
        omega
      simp [this, Finset.sum_union]
  -- Now x_i's are not necessary in this problem, we can clear them.
  clear_value g
  clear x hsum hxi H
  -- Wlog g(0) > 0.
  wlog hg0pos : g 0 > 0 generalizing g with H
  {
    -- Otherwise, we set g' := -g
    have hg0n0 : g 0 ≠ 0 := by
      intro h
      norm_num [h] at hg0
    have h' : - g 0 > 0 := by
      simp at hg0pos ⊢
      exact lt_of_le_of_ne hg0pos hg0n0
    refine H (-g) (by simp [hg0]) (by simp [hgn]) (by simp; linear_combination -hg0n) (by simpa using hgk) ?_ h'
    intro k hk
    specialize hgdiff k hk
    suffices (-g) (k + 1) - (-g) k = - (g (k + 1) - g k) by rwa [this, abs_neg]
    simp
    ring
  }
  -- Since g(0) + g(n) = 0, there is a contradiction if ∀ k ≤ n, g(k) > 0.
  suffices ∀ k ≤ n, g k > 0 by linarith [this n (by simp)]
  -- We prove by induction.
  intro k
  induction k with
  | zero => simp [hg0pos]
  | succ k ih =>
    intro hk
    specialize ih (by omega)
    specialize hgdiff k hk
    have h₁ := hgk k (by omega)
    have h₂ := hgk (k + 1) hk
    by_contra! h₃
    -- Eliminate the absolute values.
    rw [abs_of_pos ih] at h₁
    rw [abs_of_nonpos h₃] at h₂
    rw [abs_le] at hgdiff
    linarith
