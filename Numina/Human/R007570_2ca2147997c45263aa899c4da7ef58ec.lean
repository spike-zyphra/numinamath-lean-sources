import Mathlib

/- 2. Prove that if for any value of $x$ and constant $c$ the equality $f(x+c)=\frac{2}{1+f(x)}-1$ holds, then $f(x)$ is a periodic function. -/
theorem algebra_113064 {f : ℝ → ℝ} (c : ℝ)
    (h0 : ∀ x, 1 + f x ≠ 0)
    (h : ∀ x, f (x + c) = 2 / (1 + f x) - 1) :
    ∃ c, Function.Periodic f c := by
  -- f(x + c) = 2 / (1 + f(x)) - 1 implies that f(x + c) = (1 - f(x)) / (1 + f(x)).
  have hf x : f (x + c) = (1 - f x) / (1 + f x) := by rw [h]; field_simp [h0 x]; ring
  -- Prove that f is periodic with period 2c.
  use 2 * c
  intro x
  calc
    -- We have f(x + 2c) = f(x + c + c) = (1 - f(x + c)) / (1 + f(x + c))
    --                   = (1 - (1 - f(x)) / (1 + f(x))) / (1 + (1 - f(x)) / (1 + f(x)))
    --                   = f(x).
    f (x + 2 * c) = (1 - f (x + c)) / (1 + f (x + c)) := by
        rw [show x + 2 * c = x + c + c by ring, hf]
    _ = (1 - (1 - f x) / (1 + f x)) / (1 + (1 - f x) / (1 + f x)) := by rw [hf]
    _ = f x := by field_simp [h0 x]; ring