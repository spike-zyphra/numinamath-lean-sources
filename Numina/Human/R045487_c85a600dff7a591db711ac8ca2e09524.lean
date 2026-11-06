import Mathlib

/- Suppose $x$ and $y$ are positive real numbers such that

$$
x+\frac{1}{y}=y+\frac{2}{x}=3 .
$$

Compute the maximum possible value of $x y$.-/
theorem algebra_610497 :
    IsGreatest {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + 1 / y = 3 ∧ y + 2 / x = 3 ∧ z = x * y} (3 + Real.sqrt 7) := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- Prove that 3 + √7 is possible.
    use (5 + Real.sqrt 7) / 3, by positivity, (4 + Real.sqrt 7) / 3, by positivity
    iterate 2
      field_simp
      ring_nf
    tauto
  . -- Show that 3 + √7 is the greatest possible value.
    intro z x hx y hy h₀ h₁ h₂
    rw [h₂]
    clear z h₂
    -- We have x = 3 - 1 / y from h₀.
    apply eq_sub_of_add_eq at h₀
    -- Verify that 3y - 1 ≠ 0.
    have h₂ : 3 * y - 1 ≠ 0 := by
      by_contra!
      -- Assume 3y - 1 = 0, then x = 0, contradiction.
      simp [show y = 1 / 3 by linarith] at h₀
      linarith
    -- Substitute x = 3 - 1 / y into h₁.
    rw [h₀] at h₁
    field_simp at h₁
    -- We have 3y² - 8y + 3 = 0, and further (3y - 4)² = 7.
    replace h₁ : (3 * y - 4) ^ 2 = Real.sqrt 7 ^ 2 := by
      field_simp
      linarith
    -- We get two cases: y = (4 + √7) / 3 and y = (4 - √7) / 3.
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h₁
    -- Note that xy = 3y - 1.
    replace h₀ := congr_arg (· * y) h₀
    field_simp at h₀
    rw [h₀]
    -- Clearly, the greater value of y corresponds to the greater value of xy.
    calc
      3 * y - 1 = 3 + (3 * y - 4) := by ring
      _ ≤ 3 + Real.sqrt 7 := by
        apply add_le_add_left
        rcases h₁ with (h₁ | h₁)
        all_goals
          rw [h₁]
          try linarith [show 0 ≤ Real.sqrt 7 by positivity]
