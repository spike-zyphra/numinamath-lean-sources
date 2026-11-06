import Mathlib

open Finset Real Nat

/-∏ i ∈ Icc 2 n, logb i (i + 1) = 10, find n -/

theorem algebra_167760 {n : ℕ} (hn : 2 ≤ n)
(h: ∏ i ∈ Icc 2 n, logb i (i + 1) = 10): n = 1023 := by

  -- we first simplify the product
  have h_eq: ∀ m: ℕ, 2 ≤ m → ∏ i ∈ Icc 2 m, logb i (i + 1) = logb 2 (m + 1) := by
    -- prove by induction
    intro m hm
    induction' m with m ih
    -- base case
    .
      norm_num at hm
    .
      by_cases l: m = 1
      .
        simp [l]
      .
        replace l: 2 ≤ m := by omega
        simp [l] at ih
        rw [Finset.prod_Icc_succ_top]
        rw [ih]
        clear * - l
        have eq: ↑(m + 1) = ↑m + (1: ℝ) := by
          norm_cast
        rw [eq]
        repeat rw [Real.logb.eq_1]
        have o1:  Real.log 2 ≠ 0 := by
          norm_num
        have o2:  Real.log (m + 1) ≠ 0 := by
          rify at l
          norm_num
          rify
          constructor
          .
            linarith
          .
            constructor
            .
              linarith
            .
              linarith
        field_simp
        ring
        omega

  -- then we can find the value of n
  specialize h_eq n hn
  rw [h_eq] at h
  clear h_eq
  rw [Real.logb_eq_iff_rpow_eq] at h
  norm_num at h
  norm_cast at h
  omega
  norm_num
  norm_num
  rify at hn
  linarith