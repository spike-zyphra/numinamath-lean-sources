import Mathlib

/- 9. If the positive real numbers $\mathbf{x}$ and $\mathbf{y}$ satisfy $x^{3}+y^{3}=(4 x-5 y) y$, then the maximum value of $\mathbf{y}$ is -/
theorem algebra_220609 :
    IsGreatest {y : ℝ | 0 < y ∧ ∃ x, 0 < x ∧ x ^ 3 + y ^ 3 = (4 * x - 5 * y) * y} (1 / 3) := by
  simp only [IsGreatest, Set.mem_setOf_eq, inv_pos, Nat.ofNat_pos, upperBounds, and_imp, forall_exists_index]
  constructor
  -- Show that y = 1 / 3 satisfies all requirements.
  · norm_num
    -- Let x = 2 / 3 and show that x^3 + y^3 = (4 * x - 5 * y) * y.
    use 2 / 3
    norm_num
  -- Suppose that x^3 + y^3 = (4 * x - 5 * y) * y for some positive x and y.
  -- Show that y ≤ 1 / 3.
  intro y hy x hx eq
  -- Define k = x / y.
  set k := x / y
  -- Show that y = (4 * k - 5) / (k^3 + 1).
  have h : y = (4 * k - 5) / (k ^ 3 + 1) := by
    field_simp [k]
    linear_combination y ^ 2 * eq
  -- Show that 1 / 3 - (4 * k - 5) / (k^3 + 1) ≥ 0.
  rw [← sub_nonneg, ← ge_iff_le]
  calc
    1 / 3 - y = 1 / 3 - (4 * k - 5) / (k ^ 3 + 1) := by rw [h]
    -- We have 1 / 3 - (4 * k - 5) / (k^3 + 1) = (k - 2)^2 * (k + 4) / (3 * (k^3 + 1)).
    _ = (k - 2) ^ 2 * (k + 4) / (3 * (k ^ 3 + 1)) := by
      field_simp
      ring
    -- (k - 2)^2 * (k + 4) / (3 * (k^3 + 1)) ≥ 0 because k = x / y > 0.
    _ ≥ 0 := by positivity