import Mathlib
theorem algebra_14014  (f : ℝ → ℝ) (hf : f = fun z => -4 * z ^ 2 + 20 * z - 6) :
    IsGreatest (Set.image f (Set.univ : Set ℝ)) 19 := by
  have h1 : ∀ x, f x = -4 * (x - 5/2) ^ 2 + 19 := by
    intro x
    rw [hf]
    simp
    ring_nf

  -- Show that 19 is achievable as a value of f
  have h2 : 19 ∈ Set.image f (Set.univ : Set ℝ) := by
    use 5 / 2
    rw [h1]
    norm_num

  have h3 : ∀ y ∈ Set.image f (Set.univ : Set ℝ), y ≤ 19 := by
    intro y hy
    obtain ⟨x, hx⟩ := hy
    rw [h1] at hx
    have h : (x - 5/2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith

  exact ⟨h2, h3⟩