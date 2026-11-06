import Mathlib

theorem algebra_10264 (f : ℝ → ℝ) (hf : f = fun x => abs (x + 7) - abs (x - 2)) :
    Set.range f = {y | -9 ≤ y ∧ y ≤ 9} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y ∈ range f
    intro hy
    rcases hy with ⟨x, hx⟩
    by_cases h1 : x < -7
    · -- Case 1: x < -7
      rw [abs_of_neg (show x + 7 < 0 by linarith), abs_of_neg (show x - 2 < 0 by linarith)] at hx
      constructor
      · linarith
      · linarith
    · -- Case 2: x ≥ -7
      by_cases h2 : x ≤ 2
      · -- Subcase 2a: -7 ≤ x ≤ 2
        rw [abs_of_nonneg (show x + 7 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at hx
        constructor
        · linarith
        · linarith
      · -- Subcase 2b: x > 2
        rw [abs_of_nonneg (show x + 7 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith)] at hx
        constructor
        · linarith
        · linarith
  · -- Assume y ∈ [-9, 9]
    rintro ⟨hy1, hy2⟩
    use (y - 5) / 2
    have hx1 : -7 ≤ (y - 5) / 2 := by
      linarith
    have hx2 : (y - 5) / 2 ≤ 2 := by
      linarith
    have h1 : abs (( (y - 5) / 2 ) + 7) = ( (y - 5) / 2 ) + 7 := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (( (y - 5) / 2 ) - 2) = - ( ( (y - 5) / 2 ) - 2) := by
      rw [abs_of_nonpos]
      linarith
      <;> linarith
    simp [h1, h2]
    <;> linarith