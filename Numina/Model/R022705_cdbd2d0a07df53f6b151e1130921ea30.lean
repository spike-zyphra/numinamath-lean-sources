import Mathlib

theorem inequalities_142248 (k : ℕ) (hk : 2 ≤ k) :
    (1 / (k ^ 2 : ℝ)) ≤ (1 / (k - 1 : ℝ)) - (1 / k : ℝ) := by
  have h1 : (k : ℝ) ≥ 2 := by
    exact_mod_cast hk
  have h2 : (k - 1 : ℝ) ≥ 1 := by
    have h1' : (k : ℝ) ≥ 2 := by
      exact_mod_cast hk
    linarith
  have h6 : (1 / (k - 1 : ℝ)) - (1 / (k : ℝ)) = (1 / ((k : ℝ) * ((k - 1 : ℝ)))) := by
    field_simp [(show (k : ℝ) - 1 ≠ 0 by
      have h4' : (k : ℝ) - 1 ≥ 1 := by
        have h1' : (k : ℝ) ≥ 2 := by
          exact_mod_cast hk
        linarith
      linarith
    ), (show (k : ℝ) ≠ 0 by
      have h1' : (k : ℝ) ≥ 2 := by
        exact_mod_cast hk
      linarith
    )
    ]
    <;> ring
  rw [h6]
  have h7 : 0 < (k : ℝ) * (k - 1 : ℝ) := by
    nlinarith [sq_nonneg (k : ℝ), sq_nonneg ((k - 1 : ℝ)), h1]
  have h8 : 0 < (k ^ 2 : ℝ) := by
    nlinarith [sq_nonneg (k : ℝ), h1]
  apply (one_div_le_one_div (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (k : ℝ), sq_nonneg ((k - 1 : ℝ)), h1]