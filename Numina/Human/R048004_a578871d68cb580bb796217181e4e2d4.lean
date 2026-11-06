import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all real numbers $x, y$:


$$

f(x-f(y))=1-x-y

$$
 -/
theorem algebra_123417 (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔ ∀ x, f x = (1 / 2) - x := by
  constructor
  -- prove that f(x - f(y)) = 1 - x - y implies that f(x) = 1 / 2 - x
  · intro h x
    -- we have f 0 = f (f 0 - f 0) = 1 - f 0
    -- so f 0 = 1 / 2
    have f0 : f 0 = 1 - f 0 := calc
      f 0 = f (f 0 - f 0) := by simp
      _   = 1 - f 0 := by rw [h, sub_zero]
    -- we compute
    -- f x = f (x + f 0 - f 0) = 1 - (x + f 0) - 0 = 1 / 2 - x
    calc
      f x = f (x + f 0 - f 0) := by simp
      _   = 1 - (x + f 0) - 0 := by rw[h]
      _   = 1 / 2 - x := by linarith
  -- check that f(x) = 1 / 2 - x works
  · intro h x y
    rw [h, h]
    ring