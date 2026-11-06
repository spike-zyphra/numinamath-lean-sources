import Mathlib

/- Determine the functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all $x, y \in \mathbb{R}$


$$

f(x+y)=f(x)-f(y)

$$
 -/
theorem algebra_117248 (f : ℝ → ℝ) : (∀ x y, f (x + y) = f x - f y) ↔ ∀ x, f x = 0 := by
    constructor
    -- we first prove that f (x + y) = f x - f y implies f = 0
    · intro h
      -- We can switch places of x and y
      -- then we have two equations:
      -- f (y + x) = f x - f y
      -- f (y + x) = f y - f x
      have swapped : ∀ x y, f (y + x) = f x - f y
        := fun x y => add_comm x y ▸ h x y

      -- add together the two equations
      have summed : ∀ x y, f (y + x) + f (y + x) = (f x - f y) + (f y - f x) := by
        intro x y
        rw [←h y x, ←swapped x y]

      -- but the RHS is equal to zero, so f (y + x) = 0
      simp only [sub_add_sub_cancel, sub_self, add_self_eq_zero] at summed

      -- so given any argument x', we have f (x') = f (x' + 0) = 0
      intro x'
      exact zero_add x' ▸ summed x' 0
    -- if f = 0, f (x + y) = f x - f y
    · intro f_eq_zero x y
      rw [f_eq_zero (x + y), f_eq_zero x, f_eq_zero y]
      -- 0 = 0 - 0
      exact zero_sub_zero.symm