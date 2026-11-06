import Mathlib

/- 26. (YUG 4) Prove that the functional equations  $$ \begin{aligned} f(x+y) & =f(x)+f(y) \\ \text { and } \quad f(x+y+x y) & =f(x)+f(y)+f(x y) \quad(x, y \in \mathbb{R}) \end{aligned} $$  are equivalent. -/
theorem algebra_23743 (f : ℝ → ℝ) :
    (∀ x y, f (x + y) = f x + f y) ↔ (∀ x y, f (x + y + x * y) = f x + f y + f (x * y)) := by
  constructor
  <;> intro h x y
  . -- First assume that f(x + y) = f(x) + f(y) for all reals.
    -- We simply apply the functional equation twice.
    rw [h, h]
  . -- Now assume that f(x + y + xy) = f(x) + f(y) + f(xy) for all reals.
    -- Show that f(0) = 0 by plugging in x = y = 0.
    have h₀ := h 0 0
    simp at h₀
    -- Show that f(x) = -f(-x) by plugging in y = -1.
    have h₁ (x : ℝ) : f x = -f (-x) := by
      specialize h x (-1)
      simp at h
      linarith
    -- Show that f(2x + 1) = 2f(x) + f(1) by plugging in y = 1.
    have h₂ (x : ℝ) : f (2 * x + 1) = 2 * f x + f 1 := by
      specialize h x 1
      ring_nf at h ⊢
      linarith
    -- Show that f(u(2v + 1)) = 2f(uv) + f(u) for all reals.
    have h₃ (u v : ℝ) : f (u * (2 * v + 1)) = 2 * f (u * v) + f u := by
      suffices f u + 2 * f v + f 1 + f (u * (2 * v + 1)) = 2 * f (u * v) + 2 * f u + 2 * f v + f 1 by
        -- Add to both sides by f(u) + 2f(v) + f(1).
        linarith
      calc
        _ = f (u + (2 * v + 1) + u * (2 * v + 1)) := by
          -- The expression is equal to f(u + (2v + 1) + u(2v + 1)).
          rw [h, h₂]
          ac_rfl
        _ = f (2 * (u + v + u * v) + 1) := by
          -- Which is equal to f(2(u + v + uv) + 1).
          ring_nf
        _ = 2 * f (u * v) + 2 * f u + 2 * f v + f 1 := by
          -- Which is equal to the right hand side.
          rw [h₂, h]
          ring
    -- Substitute u = 2x and v = -1 / 2 and simplyf to get f(2x) = 2f(x).
    have h₄ (x : ℝ) : f (2 * x) = 2 * f x := by
      specialize h₃ (2 * x) (-1 / 2)
      specialize h₁ x
      ring_nf at h₃ ⊢
      linarith
    -- Substitute f(2x) = 2f(x) into h₃.
    replace h₃ (u v : ℝ) : f (u * (2 * v + 1)) = f (2 * (u * v)) + f u := by
      rw [h₄, h₃]
    by_cases hxy : x = 0 ∨ y = 0
    . -- Suppose x = 0 or y = 0, then it is trivial.
      rcases hxy with (h' | h')
      <;> simp [h', h₀]
    . -- For non-zero x and y, substitute u = y and v = x / (2u).
      push_neg at hxy
      specialize h₃ y (x / (2 * y))
      -- Simplify to get f(x + y) = f(x) + f(y).
      rw [show y * (2 * (x / (2 * y)) + 1) = x + y by field_simp [show 2 * y ≠ 0 by simp [hxy]]; ring, show 2 * (y * (x / (2 * y))) = x by  field_simp [show 2 * y ≠ 0 by simp [hxy]]; ring] at h₃
      exact h₃