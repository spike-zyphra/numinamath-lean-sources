import Mathlib

/- Let the function \( f: \mathbf{R} \rightarrow \mathbf{R} \) satisfy \( f(0)=1 \) and for any \( x, y \in \mathbf{R} \), it holds that \( f(xy+1) = f(x) f(y) - f(y) - x + 2 \). Determine the function \( f(x) = \quad .\)-/
theorem algebra_4015 {f : ℝ → ℝ} (h0 : f 0 = 1) : (∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) ↔
    ∀ x, f x = x + 1 := by
  constructor
  . intro h x
    have : ∀ x y, f x + y = f y + x := by
      intro x y
  --     The problem notes:
  --  \[
  --  f(xy + 1) = f(y) f(x) - f(x) - y + 2
  --  \]
      have hxy := h x y
  --     Equate this to the original equation:
  --  \[
  --  f(xy + 1) = f(x) f(y) - f(y) - x + 2
  --  \]
      have hyx := h y x
  --     Simplifying gives:
  --  \[
  --  f(x) f(y) - f(y) - x + 2 = f(y) f(x) - f(x) - y + 2
  --  \]
      rw [mul_comm x y, hyx, mul_comm (f y)] at hxy
  --     Cancelling common terms:
  --  \[
  --  -f(y) - x = -f(x) - y
  --  \]
  --  Rearrange:
  --  \[
  --  f(x) + y = f(y) + x
  --  \]
      rwa [add_right_cancel_iff, sub_sub, sub_sub, sub_right_inj] at hxy
  --   Set \( y = 0 \) again:
  --  \[
  --  f(x) + 0 = f(0) + x
  --  \]
  --  Substituting \( f(0) = 1 \):
  --  \[
  --  f(x) = x + 1
  --  \]
    rw [← add_zero (f x), add_comm x, ← h0]
    exact this x 0
  -- Let's verify if \( f(x) = x + 1 \) satisfies the given functional equation.
  intro h x y
  rw [h (x * y + 1), h x, h y]
  ring
