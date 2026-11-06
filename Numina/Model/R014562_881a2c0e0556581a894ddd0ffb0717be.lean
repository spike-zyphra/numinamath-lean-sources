import Mathlib

theorem number_theory_103980 (x y : ℕ) :
    IsSquare ((x + y) ^ 2 + 3 * x + y + 1) ↔ (x, y) = (x, x) := by
  constructor
  · -- Assume (x + y) ^ 2 + 3 * x + y + 1 is a perfect square, prove (x, y) = (x, x)
    intro h
    rcases h with ⟨z, h1⟩
    have h2 : z ≥ x + y + 1 := by
      by_contra h2
      push_neg at h2
      have h3 : z ≤ x + y := by
        omega
      have h4 : z ≤ x + y := h3
      have h5 : z ^ 2 ≤ (x + y) ^ 2 := by nlinarith
      have h6 : (x + y) ^ 2 < (x + y) ^ 2 + 3 * x + y + 1 := by
        nlinarith
      have h7 : (x + y) ^ 2 < z ^ 2 := by
        nlinarith
      have h8 : z > x + y := by
        nlinarith
      omega
    -- Show z = x + y + 1
    have h3 : z ≤ x + y + 1 := by
      by_contra h3
      push_neg at h3
      have h4 : z ≥ x + y + 2 := by
        omega
      have h4 : z ≥ x + y + 2 := h4
      have h5 : z ^ 2 ≥ (x + y + 2) ^ 2 := by nlinarith
      nlinarith
    have h4 : z = x + y + 1 := by
      omega
    -- Substitute z = x + y + 1 into the equation
    rw [h4] at h1
    have h5 : x = y := by
      have h5 : (x + y) ^ 2 + 3 * x + y + 1 = (x + y + 1) ^ 2 := by
        linarith
      nlinarith
    simp [Prod.ext_iff, h5]
  · -- Show that if (x, y) = (x, x), then the expression is a perfect square
    rintro ⟨rfl, rfl⟩
    use 2 * x + 1
    all_goals
      ring_nf