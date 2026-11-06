import Mathlib

theorem algebra_324612 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    Real.sqrt ((x - 1/x)^2 + 4) - Real.sqrt ((x + 1/x)^2 - 4) = 2 * x := by
  have h1 : 0 < x := hx.1
  have h2 : x < 1 := hx.2

  -- Compute the first square root
  have h3 : (x - 1 / x) ^ 2 + 4 = (x + 1 / x) ^ 2 := by
    field_simp
    <;> nlinarith

  -- Rewrite the first square root using the equality
  have h4 : Real.sqrt ((x - 1 / x) ^ 2 + 4) = Real.sqrt ((x + 1 / x) ^ 2) := by
    rw [h3]

  -- Simplify the square root of the square
  have h5 : Real.sqrt ((x + 1 / x) ^ 2) = abs (x + 1 / x) := by
    rw [Real.sqrt_sq_eq_abs]

  -- Simplify the first square root further by removing the abs
  have h7 : abs (x + 1 / x) = x + 1 / x := by
    have hx2 : x + 1 / x > 0 := by
      have hx1 : x > 0 := h1
      have hx3 : 1 / x > 0 := by
        apply div_pos
        linarith
        linarith
      linarith
    rw [abs_of_pos hx2]

  -- Therefore, the first square root simplifies to x + 1 / x
  have h8 : Real.sqrt ((x - 1 / x) ^ 2 + 4) = x + 1 / x := by
    rw [h4, h5, h7]

  -- Compute the second square root
  have h9 : (x + 1 / x) ^ 2 - 4 = (x - 1 / x) ^ 2 := by
    field_simp
    <;> nlinarith

  -- Rewrite the second square root using the equality
  have h10 : Real.sqrt ((x + 1 / x) ^ 2 - 4) = Real.sqrt ((x - 1 / x) ^ 2) := by
    rw [h9]

  -- Simplify the square root of the square to abs
  have h11 : Real.sqrt ((x - 1 / x) ^ 2) = abs (x - 1 / x) := by
    rw [Real.sqrt_sq_eq_abs]

  -- Simplify the second square root further by computing the abs
  have h13 : x - 1 / x < 0 := by
    have hx4 : 1 / x > 1 := by
      have hx5 : 0 < x := h1
      have hx6 : x < 1 := h2
      have hx7 : 1 / x - 1 > 0 := by
        have h12 : 1 / x - 1 = (1 - x) / x := by
          field_simp
          <;> ring
        rw [h12]
        apply div_pos
        linarith
        linarith
      linarith
    linarith

  have h14 : abs (x - 1 / x) = (1 / x - x) := by
    have h15 : abs (x - 1 / x) = abs ((x - 1 / x : ℝ)) := by rfl
    have h16 : abs ((x - 1 / x : ℝ)) = -(x - 1 / x) := by
      rw [abs_of_neg h13]
      all_goals linarith
    have h17 : -(x - 1 / x) = 1 / x - x := by linarith
    rw [h16, h17]

  -- Therefore, the second square root simplifies to (1 / x - x)
  have h18 : Real.sqrt ((x + 1 / x) ^ 2 - 4) = 1 / x - x := by
    rw [h10, h11, h14]

  -- The original expression simplifies to 2 * x
  rw [h8, h18]
  have h19 : 1 / x > 0 := by
    apply div_pos
    norm_num
    all_goals linarith

  field_simp
  <;> nlinarith