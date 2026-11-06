import Mathlib

theorem inequalities_133379 (f : ℝ → ℝ) :
    (∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + 3 * z)) ↔
    ∃ c, ∀ x, f x = c := by
  constructor
  · -- Assume the inequality holds, prove that f is constant
    intro h
    have h1 : ∀ x, f x ≤ f 0 := by
      intro x
      have h2 := h x 0 0
      simp at h2
      linarith
    have h2 : ∀ x, f 0 ≤ f x := by
      intro x
      specialize h x (-x / 2) 0 
      have h3 : x + (-x / 2) = x / 2 := by ring
      have h4 : -x / 2 + (0 : ℝ) = -x / 2 := by ring
      have h5 : (0 : ℝ) + x = x := by ring
      have h6 : x + 2 * (-x / 2) + 3 * (0 : ℝ) = 0 := by ring
      rw [h3, h4, h5, h6] at h
      linarith [h1 (x / 2), h1 (-x / 2), h1 x]
    use f 0
    intro x
    linarith [h1 x, h2 x]
  · -- Assume that there exists a constant c such that f(x) = c for all x
    rintro ⟨c, hc⟩
    intro x y z
    have h1 : f (x + y) = c := by
      apply hc
    have h2 : f (y + z) = c := by
      apply hc
    have h3 : f (z + x) = c := by
      apply hc
    have h4 : f (x + 2 * y + 3 * z) = c := by
      apply hc
    linarith [h1, h2, h3, h4]