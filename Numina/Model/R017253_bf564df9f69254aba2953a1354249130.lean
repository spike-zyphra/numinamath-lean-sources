import Mathlib

theorem algebra_104934 (f : ℝ → ℝ) :
    (∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2)) ↔
    ∃ c, ∀ x, f x = x ^ 3 + c * x := by
  constructor
  · -- Assume the functional equation holds, prove the form of f
    intro h
    have h1 : f 0 = 0 := by
      specialize h 1 1
      norm_num at h
      linarith
    have h2 : ∀ u v, v * f u - u * f v = (u ^ 2 - v ^ 2) * (u * v) := by
      intro u v
      have h2 := h ((u + v) / 2) ((u - v) / 2)
      simp [show ( (u + v) / 2 + (u - v) / 2 ) = u by ring, show ( (u + v) / 2 - (u - v) / 2 ) = v by ring] at h2
      ring_nf at h2 ⊢
      linarith [h2]
    use f 1 - 1
    intro x
    have eq1 := h2 x 1
    simp at eq1
    linarith [eq1]
  · -- Show that the form of f satisfies the functional equation
    rintro ⟨c, hc⟩
    intro x y
    have hfx1 : f (x + y) = (x + y) ^ 3 + c * (x + y) := by
      rw [hc]
    have hfx2 : f (x - y) = (x - y) ^ 3 + c * (x - y) := by
      rw [hc]
    rw [hfx1, hfx2]
    ring