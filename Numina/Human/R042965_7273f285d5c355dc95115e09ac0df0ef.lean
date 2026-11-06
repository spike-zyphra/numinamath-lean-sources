import Mathlib

/- Three, (10 points) Given
$$
\frac{x}{y+z+u}=\frac{y}{z+u+x}=\frac{z}{u+x+y}=\frac{u}{x+y+z} \text {. }
$$

Find the value of $\frac{x+y}{z+u}+\frac{y+z}{u+x}+\frac{z+u}{x+y}+\frac{u+x}{y+z}$. -/
theorem algebra_303452 {x y z u : ℝ} (h₀ : y + z + u ≠ 0) (h₁ :  z + u + x≠ 0)
    (h₂ :  u + x + y≠ 0) (h₃ : x + y + z≠ 0) (h₄ : x / (y + z + u) = y / (z + u + x))
    (h₅ : y / (z + u + x) = z / (u + x + y)) (h₆ : z / (u + x + y) = u / (x + y + z)) (hn1 : x+y≠ 0)(hn2 : y+z≠ 0)(hn3 : z+u≠ 0)(hn4 : u+x≠ 0):
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = 4 ∨
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = -4 := by
  -- Define a constant k = x / (y + z + u)
  let k := x / (y + z + u)
  have hk :k= x / (y + z + u) := by
    unfold k
    exact rfl
  -- From the given conditions, express y, z, u also in terms of k
  have hky : k = y / (z + u + x) := by
    rw [←h₄]
  have hkz : k = z / (u + x + y) := by
    rw [←h₅]
    rw [hky]
  have hku : k = u / (x + y + z) := by
    rw [←h₆]
    rw [hkz]
  -- Rewrite x, y, z, u in terms of k and sums of other variables
  have h_x : x = k * (y + z + u) := by
    unfold k
    simp[div_mul_cancel₀ x h₀]
  have h_y : y = k * (z + u + x) := by
    rw [hky]
    simp [div_mul_cancel₀ y h₁]
  have h_z : z = k * (u + x + y) := by
    rw [hkz]
    simp [div_mul_cancel₀ z h₂]
  have h_u : u = k * (x + y + z) := by
    rw [hku]
    simp [div_mul_cancel₀ u h₃]

  -- Compute the sum x + y + z + u
  have h_sum : x + y + z + u = k * (y + z + u) + k * (z + u + x) + k * (u + x + y) + k * (x + y + z) := by
    linarith
  -- Simplify the sum to a form involving k * (x + y + z + u) * 3
  have h_sum_simp : x + y + z + u = k * (x + y + z + u) * 3 := by
    have : k * (x + y + z + u) * 3 = k * (y + z + u) + k * (z + u + x) + k * (u + x + y) + k * (x + y + z) := by
      linarith
    rw [this]
    exact h_sum
  -- Consider two cases: whether x + y + z + u = 0 or not
  by_cases h_sum_zero : x + y + z + u = 0

  -- Case 1: x + y + z + u = 0
  ·
    -- In this case, derive relationships between sums of variables
    have h_xy_zu : x + y = -(z + u) := by
      linarith
    have h_yz_ux : y + z = -(u + x) := by
      linarith
    have h_zu_xy : z + u = -(x + y) := by
      linarith
    have h_ux_yz : u + x = -(y + z) := by
      linarith
    -- Calculate the final target expression
    have h_result : (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = -4 := by
      have h1 : (x + y) / (z + u) = -1 := by
        rw[h_xy_zu]
        rw[neg_div_self hn3]
      have h2 : (y + z) / (u + x) = -1 := by
        rw[h_yz_ux]
        rw[neg_div_self hn4]
      have h3 : (z + u) / (x + y) = -1 := by
        rw[h_zu_xy]
        rw[neg_div_self hn1]
      have h4 : (u + x) / (y + z) = -1 := by
        rw[h_ux_yz]
        rw[neg_div_self hn2]
      rw [h1, h2, h3, h4]
      norm_num
    right
    exact h_result

  -- Case 2: x + y + z + u ≠ 0
  ·
    -- From h_sum_simp, deduce that k = 1/3
    have h_k : k = 1 / 3 := by
      have h_factor : x + y + z + u - k * (x + y + z + u) * 3 = 0 := by
        linarith
      have h_factor_simp : (x + y + z + u) * (1 - 3 * k) = 0 := by
        linarith
      have h_k_val : 1 - 3 * k = 0 := by
        have h_sum_nonzero : x + y + z + u ≠ 0 := by
          exact h_sum_zero
        exact (mul_eq_zero.mp h_factor_simp).resolve_left h_sum_nonzero
      field_simp at h_k_val
      linarith
    -- Substitute k = 1/3 into expressions for x, y, z, u
    rw[h_k]at h_x
    rw[h_k]at h_y
    rw[h_k]at h_z
    rw[h_k]at h_u
    -- Show that x = y = z = u
    have h_eq_xyz : x = y := by
      linarith
    have h_eq_yz : y = z := by
      linarith
    have h_eq_zu : z = u := by
      linarith
    have h_all_equal : x = y ∧ y = z ∧ z = u := by
      constructor
      · exact h_eq_xyz
      constructor
      · exact h_eq_yz
      · exact h_eq_zu
    -- Ensure denominator is nonzero
    have hnn : u+u≠ 0 := by
      have :u+u=z+u := by
        linarith
      rw [this]
      exact hn3
    -- Calculate the final target expression
    have h_result : (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = 4 := by
      rw [h_all_equal.1, h_all_equal.2.1, h_all_equal.2.2]
      simp[div_self hnn]
      norm_num
    left
    exact h_result
