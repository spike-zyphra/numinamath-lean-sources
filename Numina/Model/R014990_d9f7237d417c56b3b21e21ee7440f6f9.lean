import Mathlib

theorem algebra_276162 (n : ℕ) (hn : n ≠ 0) (h : Real.sqrt (∏ i ∈ Finset.Icc 1 n, (2 * i + 1) / (2 * i - 1)) = 9) :
    n = 40 := by

  have h1 : (∏ i in Finset.Icc 1 n, (2 * i + 1) / (2 * i - 1) : ℝ) = (2 * (n : ℝ) + 1) := by
    have h10 : ∀ (n : ℕ), (∏ i in Finset.Icc 1 n, (2 * i + 1) / (2 * i - 1) : ℝ) = (2 * (n : ℝ) + 1) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [(show ((2 * ((↑n : ℝ) + 1) - 1 : ℝ)) ≠ 0 by
          have h15 : (↑n : ℝ) ≥ (0 : ℝ) := by positivity
          nlinarith
        )
        ]
        <;> ring_nf 
    specialize h10 n
    simpa using h10

  have h2 : Real.sqrt (∏ i ∈ Finset.Icc 1 n, (2 * i + 1) / (2 * i - 1)) = 9 := h
  rw [h1] at h2

  have h3 : Real.sqrt ((2 * (n : ℝ) + 1 : ℝ)) = 9 := by
    simpa using h2

  have h4 : (2 * (n : ℝ) + 1 : ℝ) ≥ 0 := by
    have h60 : (2 * (n : ℝ) + 1 : ℝ) ≥ (1 : ℝ) := by
      have h6k : (n : ℝ) ≥ (0 : ℝ) := by positivity
      nlinarith
    nlinarith

  have h5 : ((2 * (n : ℝ) + 1 : ℝ) ) = (81 : ℝ) := by
    have h6 : Real.sqrt ((2 * (n : ℝ) + 1 : ℝ)) = 9 := h3
    have h7 : Real.sqrt ((2 * (n : ℝ) + 1 : ℝ)) ^ 2 = (9 : ℝ) ^ 2 := by
      rw [h6]
    have h7m : Real.sqrt ((2 * (n : ℝ) + 1 : ℝ)) ^ 2 = (2 * (n : ℝ) + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals positivity
    rw [h7m] at h7
    nlinarith

  have h9 : (n : ℝ) = (40 : ℝ) := by
    linarith

  have h10 : (n : ℕ) = 40 := by
    exact_mod_cast h9

  exact h10