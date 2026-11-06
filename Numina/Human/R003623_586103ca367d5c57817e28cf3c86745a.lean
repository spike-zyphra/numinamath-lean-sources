import Mathlib

open Real Set
open scoped BigOperators

/- 14. Let $x, y, z$ be positive real numbers, and $x+y+z=1$. Find the minimum value of the function $f(x, y, z)=\frac{3 x^{2}-x}{1+x^{2}}+\frac{3 y^{2}-y}{1+y^{2}}+\frac{3 z^{2}-z}{1+z^{2}}$, and provide a proof. -/
theorem algebra_202411 :
  IsLeast {t | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧ t = (3 * x ^ 2 - x) / (1 + x ^ 2) +
    (3 * y ^ 2 - y) / (1 + y ^ 2) + (3 * z ^ 2 - z) / (1 + z ^ 2)} 0 := by
  unfold IsLeast
  constructor
  · -- Show that 0 is attained when x = y = z = 1/3
    simp
    repeat
      use (1 / 3 : ℝ)
      norm_num
  -- Show that 0 is a lower bound
  -- Prove a tangent line bound
  have line_ineq : ∀ x ∈ Ioo (0 : ℝ) 1, (3 * x^2 - x) / (1 + x^2) ≥ 3 / 10 * (3 * x - 1) := by
    intro x hx
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    field_simp
    rw [div_le_iff₀ (by positivity)]
    -- Factor the inequality
    suffices (1 - 3 * x)^2 * (x - 3) ≤ 0 by
      linarith
    -- Show that the inequality is true by the bounds on x
    rw [mul_nonpos_iff]
    left
    constructor
    · positivity
    simp at hx
    linarith
  unfold lowerBounds
  simp
  intro a x hx y hy z hz h ha
  rw [ha]
  -- Show that x, y, z lie in Ioo 0 1
  have x_mem_Ioo : x ∈ Ioo 0 1 := by simp; exact ⟨by linarith, by linarith⟩
  have y_mem_Ioo : y ∈ Ioo 0 1 := by simp; exact ⟨by linarith, by linarith⟩
  have z_mem_Ioo : z ∈ Ioo 0 1 := by simp; exact ⟨by linarith, by linarith⟩
  rw [← ge_iff_le]
  calc
    -- Use the tangent line bound
    _ ≥ 3 / 10 * (3 * x - 1) + 3 / 10 * (3 * y - 1) + 3 / 10 * (3 * z - 1) := by linarith [line_ineq x x_mem_Ioo, line_ineq y y_mem_Ioo, line_ineq z z_mem_Ioo]
    _ = 3 / 10 * (3 * (x + y + z) - 3) := by linarith
    _ = 0 := by linarith