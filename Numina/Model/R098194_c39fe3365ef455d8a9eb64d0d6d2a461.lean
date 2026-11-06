import Mathlib

open Real

theorem algebra_196673 {f : ℝ → ℝ} (hf : f = fun x => (x + 2) / (x - 3)) :
    ∀ y, y ≠ 1 ↔ ∃ x, f x = y := by 
  intro y
  constructor
  · -- Forward direction: If y ≠ 1, then show there exists an x such that f(x) = y
    intro hy
    use (3 * y + 2) / (y - 1)
    rw [hf]
    simp
    have h1 : y - 1 ≠ 0 := by 
      intro h'
      apply hy 
      linarith 
    field_simp [h1]
    <;> ring
  · -- Backward direction: If there exists an x such that f(x) = y, then show y ≠ 1
    rintro ⟨x, hx⟩
    rw [hf] at hx 
    simp at hx 
    by_contra h
    have h1 : y = 1 := by 
      exact h
    rw [h1] at hx
    by_cases h2 : x - 3 = 0 
    · -- Case where x - 3 = 0, which means division by zero
      rw [h2] at hx
      norm_num at hx 
      all_goals linarith 
    · -- Case where x - 3 ≠ 0, we can multiply both sides
      have h2' : x - 3 ≠ 0 := by 
        exact h2 
      have eq1 : (x + 2) / (x - 3) = 1 := by 
        exact hx 
      have eq2 : x + 2 = 1 * (x - 3) := by 
        field_simp [h2'] at eq1 ⊢ 
        linarith 
      have eq3 : x + 2 = x - 3 := by 
        linarith [eq2] 
      linarith