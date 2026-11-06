import Mathlib

theorem algebra_22660 (f : ℝ → ℝ) (hf : f = λ x => abs (x - 4) + abs (x - 20) + abs (x - 50)) :
    Set.range f = {y | 46 ≤ y} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y in range f
    rintro ⟨x, hx⟩
    by_cases h1 : x ≥ 50
    · -- x ≥ 50
      rw [abs_of_nonneg (show x - 4 ≥ 0 by linarith), abs_of_nonneg (show x - 20 ≥ 0 by linarith), abs_of_nonneg (show x - 50 ≥ 0 by linarith)] at hx
      linarith
    by_cases h2 : x ≥ 20
    · -- 20 ≤ x < 50
      rw [abs_of_nonneg (show x - 4 ≥ 0 by linarith), abs_of_nonneg (show x - 20 ≥ 0 by linarith), abs_of_nonpos (show x - 50 ≤ 0 by linarith)] at hx
      linarith
    by_cases h3 : x ≥ 4
    · -- 4 ≤ x < 20
      rw [abs_of_nonneg (show x - 4 ≥ 0 by linarith), abs_of_nonpos (show x - 20 ≤ 0 by linarith), abs_of_nonpos (show x - 50 ≤ 0 by linarith)] at hx
      linarith
    · -- x < 4
      rw [abs_of_nonpos (show x - 4 ≤ 0 by linarith), abs_of_nonpos (show x - 20 ≤ 0 by linarith), abs_of_nonpos (show x - 50 ≤ 0 by linarith)] at hx
      linarith
  · -- Now for the reverse implication: if 46 ≤ y, then y ∈ range f
    intro hy
    have h2 : 46 ≤ y := by linarith
    by_cases h3 : y ≥ 76
    · -- y ≥ 76
      use (y + 74) / 3
      have h4 : (y + 74) / 3 ≥ 50 := by
        linarith
      have h5 : ((y + 74) / 3 : ℝ) - 4 ≥ 0 := by linarith
      have h6 : ((y + 74) / 3 : ℝ) - 20 ≥ 0 := by linarith
      have h7 : ((y + 74) / 3 : ℝ) - 50 ≥ 0 := by linarith
      rw [abs_of_nonneg h5, abs_of_nonneg h6, abs_of_nonneg h7]
      all_goals
        linarith
        <;> nlinarith
    · -- y < 76
      have h4 : y < 76 := by linarith
      use (y - 26 : ℝ)
      have h5 : (y - 26 : ℝ) ≥ 20 := by
        linarith
      have h6 : (y - 26 : ℝ) < 50 := by
        linarith
      have h7 : ((y - 26 : ℝ) - 4 : ℝ) ≥ 0 := by
        linarith
      have h8 : ((y - 26 : ℝ) - 20 : ℝ) ≥ 0 := by
        linarith
      have h9 : ((y - 26 : ℝ) - 50 : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonneg h7, abs_of_nonneg h8, abs_of_nonpos h9]
      all_goals
        linarith
        <;> nlinarith