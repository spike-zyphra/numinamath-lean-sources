import Mathlib

open Set Real

theorem inequalities_298890 : {a : ℝ | {x | x^2 - 3 * x + 2 ≤ 0} ⊆ {x | 1 / (x - 3) < a}} = Set.Ioi (-1/2) := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · -- Assume {x | x^2 - 3 * x + 2 ≤ 0} ⊆ {x | 1 / (x - 3) < a}
    intro h
    have h1 : (1 / (1 - 3 : ℝ)) < a := by
      have h1 : (1 : ℝ) ^ 2 - 3 * (1 : ℝ) + 2 ≤ (0 : ℝ) := by norm_num
      have h2 : (1 : ℝ) ∈ {x | 1 / (x - 3) < a} := h (by norm_num)
      simpa using h2
    norm_num at h1 ⊢
    linarith
  · -- Assume a > -1/2
    intro ha x hx
    have h4 : x ^ 2 - 3 * x + 2 ≤ 0 := by
      simp at hx ⊢
      all_goals linarith
    have h5 : 1 ≤ x := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
    have h6 : x ≤ 2 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
    have h2 : x - 3 < 0 := by
      linarith
    have h3 : 1 / (x - 3) ≤ -1 / 2 := by
      apply (div_le_iff_of_neg' (by linarith)).mpr
      nlinarith
    have h4 : 1 / (x - 3) < a := by
      linarith
    exact h4