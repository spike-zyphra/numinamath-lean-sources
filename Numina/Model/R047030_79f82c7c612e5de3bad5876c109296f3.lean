import Mathlib

theorem algebra_244150 (f : ℝ → ℝ) (h : ∀ x y, f (x + 2 * y) - f (3 * x - 2 * y) = 2 * y - x)
    (t : ℝ) (ht : t ≠ 0) :
    (f (4 * t) - f t) / (f (3 * t) - f (2 * t)) = 3 := by
  have eq1 : f (4 * t) - f t = 3 * t / 2 := by
    have h1 := h (5 * t / 4) (11 * t / 8)
    ring_nf at h1 ⊢
    linarith
  
  have eq2 : f (3 * t) - f (2 * t) = t / 2 := by
    have h2 := h (5 * t / 4) (7 * t / 8)
    ring_nf at h2 ⊢
    linarith
  
  have ht2 : f (3 * t) - f (2 * t) ≠ 0 := by
    rw [eq2]
    by_contra h'
    have h't : t = 0 := by linarith
    contradiction
  
  have h3 : f (4 * t) - f t = 3 * (f (3 * t) - f (2 * t)) := by
    rw [eq1, eq2]
    ring
  
  rw [h3]
  field_simp [ht2]
  <;> ring
  all_goals linarith