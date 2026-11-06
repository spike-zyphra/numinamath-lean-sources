import Mathlib

theorem algebra_21855 (f : ℝ → ℝ) (hf : Set.range f = Set.Icc (-11) 3)
    (g : ℝ → ℝ) (hg : ∀ x, g x = f (6 * x) + 1) :
    Set.range g = Set.Icc (-10) 4 := by
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Forward: if y ∈ range g, then y ∈ Icc (-10) 4
    intro hy
    rcases hy with ⟨x, hx⟩
    rw [hg x] at hx
    have h1 : f (6 * x) ∈ Set.range f := by
      simpa using ⟨6 * x, rfl⟩
    rw [hf] at h1
    rcases h1 with ⟨h2, h3⟩
    constructor
    · -- Show that -10 ≤ y
      linarith
    · -- Show that y ≤ 4
      linarith
  · -- Backward: if y ∈ Icc (-10) 4, then y ∈ range g
    rintro ⟨hy1, hy2⟩
    have h4 : y - 1 ∈ Set.range f := by
      rw [hf]
      constructor
      · -- Show that -11 ≤ y - 1
        linarith
      · -- Show that y - 1 ≤ 3
        linarith
    rcases h4 with ⟨z, hz⟩
    use z / 6
    rw [hg]
    have h5 : (6 * (z / 6) ) = (z : ℝ) := by ring
    rw [h5]
    rw [hz]
    all_goals linarith