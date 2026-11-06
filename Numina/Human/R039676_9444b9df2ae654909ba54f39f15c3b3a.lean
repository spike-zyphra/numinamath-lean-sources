import Mathlib

/-If $|x+5|-|3x-6|=0$, find the largest possible value of $x$. Express your answer as an improper fraction.-/
theorem algebra_22207 : IsGreatest {x : ℝ | abs (x + 5) - abs (3 * x - 6) = 0} (11 / 2) := by
  constructor
  · -- Prove that 11/2 is in the set
    simp
    norm_num
  · -- Prove that 11/2 is the greatest element
    apply mem_upperBounds.mpr
    simp
    intro x hx
    -- |x + 5| - |3 * x - 6| = 0, so, x + 5 = 3 * x - 6 or x + 5 = -(3 * x - 6)
    rw [sub_eq_zero, abs_eq_abs] at hx
    obtain (r | r) := hx <;> linarith
