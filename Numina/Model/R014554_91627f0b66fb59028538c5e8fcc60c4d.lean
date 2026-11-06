import Mathlib

theorem algebra_238184 : ¬∃ (x : ℚ), Real.sqrt (6 - 4 * Real.sqrt 2) - Real.sqrt (6 + 4 * Real.sqrt 2) = x := by
  rintro ⟨q, hq⟩
  have h1 : Real.sqrt (6 - 4 * Real.sqrt 2) = 2 - Real.sqrt 2 := by
    have h2 : (2 - Real.sqrt 2) ^ 2 = 6 - 4 * Real.sqrt 2 := by
      calc
        (2 - Real.sqrt 2) ^ 2 = 4 - 4 * Real.sqrt 2 + (Real.sqrt 2) ^ 2 := by ring
        _ = 4 - 4 * Real.sqrt 2 + 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        _ = 6 - 4 * Real.sqrt 2 := by ring
    have h3 : 0 ≤ (2 - Real.sqrt 2 : ℝ) := by
      have h4 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left]
        all_goals norm_num
      linarith
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  have h2 : Real.sqrt (6 + 4 * Real.sqrt 2) = 2 + Real.sqrt 2 := by
    have h3 : (2 + Real.sqrt 2) ^ 2 = 6 + 4 * Real.sqrt 2 := by
      calc
        (2 + Real.sqrt 2) ^ 2 = 4 + 4 * Real.sqrt 2 + (Real.sqrt 2) ^ 2 := by ring
        _ = 4 + 4 * Real.sqrt 2 + 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        _ = 6 + 4 * Real.sqrt 2 := by ring
    have h4 : 0 ≤ (2 + Real.sqrt 2 : ℝ) := by
      have h5 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    rw [← h3]
    field_simp [Real.sqrt_sq h4]
  have h3 : Real.sqrt (6 - 4 * Real.sqrt 2) - Real.sqrt (6 + 4 * Real.sqrt 2) = -2 * Real.sqrt 2 := by
    rw [h1, h2]
    ring
  rw [h3] at hq
  have h4 : Real.sqrt 2 = (- (q : ℝ) / 2) := by
    linarith
  have h5 : ∃ r : ℚ, Real.sqrt 2 = (r : ℝ) := by
    use (-q / 2)
    rw [h4]
    all_goals norm_num
  have h6 : Irrational (Real.sqrt (2 : ℕ)) := by native_decide
  have h7 : Irrational (Real.sqrt (2 : ℝ)) := by
    simpa using h6
  have h8 : ¬ Irrational (Real.sqrt (2 : ℝ)) := by
    rcases h5 with ⟨r, hr⟩
    rw [hr]
    simp
  contradiction