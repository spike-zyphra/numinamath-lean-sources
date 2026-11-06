import Mathlib

theorem number_theory_91058 (i j k : ℤ) (h : i^2 + j^2 + k^2 = 2011) :
    i + j + k ≤ 77 ∧ ∃ i j k, i^2 + j^2 + k^2 = 2011 ∧ i + j + k = 77 := by
  have h1 : (i + j + k : ℤ) ≤ 77 := by
    nlinarith [sq_nonneg (i - j), sq_nonneg (j - k), sq_nonneg (k - i)]
  constructor
  · -- Show that $i + j + k \leq 77$
    exact h1
  · -- Show that there exist $i, j, k$ such that $i^2 + j^2 + k^2 = 2011$ and $i + j + k = 77$
    refine ⟨21, 27, 29, ?_⟩
    constructor
    · -- Show that $21^2 + 27^2 + 29^2 = 2011$
      norm_num
    · -- Show that $21 + 27 + 29 = 77$
      norm_num