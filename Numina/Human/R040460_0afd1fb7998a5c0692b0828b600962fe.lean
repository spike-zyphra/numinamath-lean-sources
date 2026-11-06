import Mathlib

/-- The function $f(x)$ satisfies $f(1) = 1$ and
\[f(x + y) = 3^y f(x) + 2^x f(y)\]for all real numbers $x$ and $y.$  Find the function $f(x).$-/
theorem intermediate_algebra_4101 {f : ℝ → ℝ} (h : f 1 = 1) (h' : ∀ x y, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) :
    ∀ x, f x = 3 ^ x - 2 ^ x := by
  -- according to $f(x+y) = f(y+x)$, we get $3 ^ y * f x + 2 ^ x * f y = 3 ^ x * f y + 2 ^ y * f x$.
  have (x y : ℝ) : 3 ^ y * f x + 2 ^ x * f y = 3 ^ x * f y + 2 ^ y * f x := calc
    _ = f (x + y) := by rw [h']
    _ = f (y + x) := by rw [add_comm]
    _ = _ := by rw [h']
  -- Move items and combine similar items， we get $(3 ^ y - 2 ^ y) * f x = (3 ^ x - 2 ^ x) * f y$.
  have (x y : ℝ) : (3 ^ y - 2 ^ y) * f x = (3 ^ x - 2 ^ x) * f y := by
    rw [← sub_eq_zero]
    refine Eq.trans ?_ (sub_eq_zero.mpr (this x y))
    ring
  intro x
  -- Substituting `x = 1, y = x` into the above equation.
  have := neg_eq_zero.mpr <| sub_eq_zero.mpr (h ▸ this 1 x)
  rw [← sub_eq_zero]
  refine Eq.trans ?_ this
  ring
