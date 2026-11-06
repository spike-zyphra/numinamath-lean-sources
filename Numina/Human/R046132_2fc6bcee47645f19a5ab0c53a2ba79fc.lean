import Mathlib

/- Trouver tous les couples d'entiers relatifs $(x, y)$ tels que $x^{3}+y^{3}=(x+y)^{2}$. -/
theorem algebra_607519 :
  { (x, y) : ℤ × ℤ | x ^ 3 + y ^ 3 = (x + y) ^ 2 } = { (2, 2), (1, 2), (1, 0), (2, 1), (0, 1) } ∪ { (x, -x) | x : ℤ } := by
  ext ⟨x, y⟩
  simp
  constructor
  -- First, we verify that the elements of the set on the right are solutions.
  swap
  . rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨x, rfl⟩)
    all_goals
      simp
    ring
  -- Now, we show that any solution must be in the set on the right.
  . rintro H
    -- We consider the case where x + y = 0.
    by_cases h : x + y = 0
    {
      -- In this case, we have -x = y.
      right
      exact Int.neg_eq_of_add_eq_zero h
    }
    -- Now, we consider the case where x + y ≠ 0.
    left
    -- Factor x ^ 3 + y ^ 3 as (x + y) * (x ^ 2 - x * y + y ^ 2).
    rw [show x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2) by ring, show (x + y) ^ 2 = (x + y) * (x + y) by ring] at H
    -- Cancel the (x + y) factor on both sides.
    simp [h] at H
    -- We now have x ^ 2 - x * y + y ^ 2 = x + y.
    -- We can rewrite this as (x - 1) ^ 2 + (y - 1) ^ 2 + (x - y) ^ 2 = 2.
    replace H : (x - 1) ^ 2 + (y - 1) ^ 2 + (x - y) ^ 2 = 2 := by linear_combination 2 * H
    -- So |x - 1| ≤ 1, |y - 1| ≤ 1
    have hx : (x - 1) ^ 2 ≤ 2 := by linarith only [H, sq_nonneg (y - 1), sq_nonneg (x - y)]
    replace hx : |x - 1| ≤ 1 := by
      rw [← sq_abs] at hx
      nlinarith only [hx]
    replace hx : x = 0 ∨ x = 1 ∨ x = 2 := by
      rw [abs_le] at hx
      omega
    have hy : (y - 1) ^ 2 ≤ 2 := by linarith only [H, sq_nonneg (x - 1), sq_nonneg (x - y)]
    replace hy : |y - 1| ≤ 1 := by
      rw [← sq_abs] at hy
      nlinarith only [hy]
    replace hy : y = 0 ∨ y = 1 ∨ y = 2 := by
      rw [abs_le] at hy
      omega
    -- There are 9 possible cases, and we verify them one by one.
    rcases hx with (rfl | rfl | rfl) <;>
    rcases hy with (rfl | rfl | rfl) <;>
    all_goals
      simp at *
