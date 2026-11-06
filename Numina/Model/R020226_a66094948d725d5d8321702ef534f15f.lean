import Mathlib

theorem algebra_228128 (f : ℝ → ℝ) :
    (∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2)) ↔
    ∃ α, ∀ x, f x = x ^ 3 + α * x := by
  constructor
  · -- Assume that $f$ satisfies the functional equation for all $x, y$
    intro h
    have h1 : ∀ z w, w * f z - z * f w = z * w * (z^2 - w^2) := by
      intro z w
      have h' := h ((z + w) / 2) ((z - w) / 2)
      -- substitute x=(z+w)/2, y=(z-w)/2 into the original equation
      -- simplifying left and right side
      ring_nf at h' ⊢
      linarith
    use (f 1 - 1)
    intro x
    have eq1 := h1 x 1
    -- solving f(x)
    have eq2 : f x - x * f 1 = x * (x ^ 2 - (1 : ℝ)) := by
      nlinarith [eq1]
    calc
      f x = x * f 1 + x * (x ^ 2 - 1) := by linarith [eq2]
      _ = x ^ 3 + (f 1 - 1) * x := by ring
  · -- Now prove the converse direction.
    rintro ⟨α, h⟩
    intro x y
    have hfx1 : f (x + y) = (x + y) ^ 3 + α * (x + y) := by
      rw [h]
    have hfx2 : f (x - y) = (x - y) ^ 3 + α * (x - y) := by
      rw [h]
    rw [hfx1, hfx2]
    ring_nf