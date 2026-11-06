import Mathlib

/-E845
Let $K$ be a positive integer. If there exists an integer $n \ge 2$ such that $n(n-1)+1 \le K \le n^2-1$,
determine this integer $n$. Show that such an $n$ (if it exists) is equal to $\lceil \sqrt{K+1} \rceil$ -/

theorem number_theory_641527 (K: ℤ) (n: ℤ) (hk: 0 < K) (hn: 2 ≤ n)
 (h1: n * (n - 1) + 1 ≤ K) (h2: K ≤ n ^ 2 - 1):  n = ⌈√(K + 1)⌉ := by
  symm
  rw [Int.ceil_eq_iff]
  constructor

  -- the first direction
  .
    by_contra! h
    replace hk: 1 ≤ K := by
      omega
    replace h: K + 1 ≤ (n - 1) ^ 2 := by
      rify
      have u: K + (1: ℝ) = √(K + 1) ^ 2 := by
        rw [← Real.sqrt_eq_iff_eq_sq]
        norm_cast
        omega
        apply Real.sqrt_nonneg
      rw [u]
      rify at hk hn
      rw [sq_le_sq₀]
      .
        tauto
      .
        apply Real.sqrt_nonneg
      .
        linarith
    nlinarith

  -- the second direction
  .
    suffices K + 1 ≤ n ^ 2 by
      rify at this
      have u: (n: ℝ) = √(n ^ 2) := by
        symm
        rify at hn
        rw [Real.sqrt_eq_iff_eq_sq]
        nlinarith
        nlinarith
      rw [u]
      rw [Real.sqrt_le_sqrt_iff]
      tauto
      norm_cast
      omega
    linarith