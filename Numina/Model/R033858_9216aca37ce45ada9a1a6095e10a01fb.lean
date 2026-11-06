import Mathlib

theorem number_theory_258524 :
    {r : ℝ | ∃p q : ℕ, p.Prime ∧ q.Prime ∧
          3 * p + 5 * q = 31 ∧
          r = Real.logb 2 (p / (3 * q + 1))
    } = {-3, 0} := by

  ext r
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume that r in left side set, need prove right side set
    rintro ⟨p, q, hp, hq, heq, hr⟩
    have h1 : p ≤ 31 := by
      have : 3 * p ≤ 31 := by
        linarith [heq, show 5 * q ≥ 0 by positivity]
      omega

    have h2 : q ≤ 6 := by
      have : 5 * q ≤ 31 := by
        linarith [heq, show 3 * p ≥ 0 by positivity]
      omega
    interval_cases q <;> interval_cases p
    <;> norm_num at heq hp hq
    <;> norm_num [hr] at *
    <;> norm_num [Real.logb_eq_iff_rpow_eq] at *
    <;> norm_num at *
    <;> try { tauto }
  · -- Assume right side set, need prove left side set
    rintro (hr | hr)
    · -- r = -3
      use 2, 5
      have h1 : Real.logb 2 (2 / ((3 * (5 : ℕ) + 1 : ℝ))) = -3 := by
        norm_num [Real.logb_eq_iff_rpow_eq]
      rw [show Real.logb 2 ((2 : ℝ) / ((3 : ℝ) * ((5 : ℕ) : ℝ) + (1 : ℝ))) = Real.logb 2 (2 / ((3 * (5 : ℕ) + 1 : ℝ))) by norm_num] at *
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      linarith [h1, hr]
    · -- r = 0
      use 7, 2
      have h1 : Real.logb 2 (7 / ((3 * (2 : ℕ) + 1 : ℝ))) = 0 := by
        norm_num [Real.logb_eq_iff_rpow_eq]
      rw [show Real.logb 2 ((7 : ℝ) / ((3 : ℝ) * ((2 : ℕ) : ℝ) + (1 : ℝ))) = Real.logb 2 (7 / ((3 * (2 : ℕ) + 1 : ℝ))) by norm_num] at *
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      linarith [h1, hr]