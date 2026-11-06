import Mathlib

theorem algebra_4445 (n : ℤ) (hn : n ≥ 0) :
    (n + 1)^2 + n - Int.floor (Real.sqrt ((n + 1)^2 + n))^2 = n := by
  have h1 : (n : ℝ) ≥ 0 := by exact_mod_cast hn

  have h2 : (n + 1 : ℝ) ≤ Real.sqrt ((n + 1)^2 + (n : ℝ)) := by
    have h3 : (n + 1 : ℝ) ^ 2 ≤ (n + 1)^2 + (n : ℝ) := by
      nlinarith [sq_nonneg (n : ℝ)]
    have h4 : (n + 1 : ℝ) ≤ Real.sqrt ((n + 1)^2 + (n : ℝ)) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith

  have h3 : Real.sqrt ((n + 1)^2 + (n : ℝ)) < (n + 2 : ℝ) := by
    have h4 : (n + 1)^2 + (n : ℝ) < (n + 2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    have h5 : Real.sqrt ((n + 1)^2 + (n : ℝ)) < (n + 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg ((n + 1)^2 + (n : ℝ)), Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ)^2 + (n : ℝ) by nlinarith)]
    linarith

  have h4 : Int.floor (Real.sqrt ((n + 1)^2 + (n : ℝ)) ) = n + 1 := by
    have h5 : (n + 1 : ℝ) ≤ Real.sqrt ((n + 1)^2 + (n : ℝ)) := h2
    have h6 : Real.sqrt ((n + 1)^2 + (n : ℝ)) < (n + 2 : ℝ) := h3
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try nlinarith)
    all_goals
      try { tauto }

  rw [h4]
  nlinarith