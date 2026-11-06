import Mathlib
/-
A2 Find the maximum value of $z+x$, if $(x, y, z, t)$ satisfies the conditions:
$$
\left\{\begin{array}{l}
x^{2}+y^{2}=4 \\
z^{2}+t^{2}=9 \\
x t+y z \geq 6
\end{array}\right.
$$
-/
theorem algebra_106814 (x y z t : ℝ) (h₁ : x^2 + y^2 = 4) (h₂ : z^2 + t^2 = 9) (h₃ : x*t + y*z ≥ 6) : x + z ≤ Real.sqrt 13 := by
  -- Apply Lagrange's identity to expand the product of sums of squares
  have h_lagrange : (x^2 + y^2) * (z^2 + t^2) = (x*t + y*z)^2 + (x*z - y*t)^2 := by
    ring

  -- Substitute the known values of x^2 + y^2 and z^2 + t^2 into Lagrange's identity
  have h_sub : (4 : ℝ) * 9 = (x*t + y*z)^2 + (x*z - y*t)^2 := by
    rw [h₁, h₂] at h_lagrange
    exact h_lagrange

  -- Simplify the equation to show that the sum of squares equals 36
  have h_36_eq_sum_sq : (x*t + y*z)^2 + (x*z - y*t)^2 = 36 := by
    symm at h_sub
    norm_num at h_sub
    exact h_sub

  -- Prove that (x*t + y*z)^2 ≥ 36 using the non-negativity of squares and given inequality
  have h_sq_ge_36 : (x*t + y*z)^2 ≥ 36 := by
    have h_nonneg : x*t + y*z ≥ 0 := by
      linarith [h₃]
    nlinarith [sq_nonneg (x * t + y * z), h₃, h_nonneg]

  -- Show that (x*z - y*t)^2 ≤ 0 by leveraging the previous results
  have h_xz_yt_sq_le_0 : (x*z - y*t)^2 ≤ 0 := by
    linarith [h_36_eq_sum_sq, h_sq_ge_36]

  -- Confirm that (x*z - y*t)^2 ≥ 0 by the non-negativity of squares
  have h_xz_yt_sq_nonneg : (x*z - y*t)^2 ≥ 0 := by
    exact sq_nonneg (x*z - y*t)

  -- Conclude that (x*z - y*t)^2 = 0, implying x*z = y*t
  have h_xz_yt_sq_eq_0 : (x*z - y*t)^2 = 0 := by
    exact le_antisymm h_xz_yt_sq_le_0 h_xz_yt_sq_nonneg

  -- Derive the equality x*z = y*t from the squared term being zero
  have h_xz_eq_yt : x*z - y*t = 0 := by
    rw [sq_eq_zero_iff] at h_xz_yt_sq_eq_0
    exact h_xz_yt_sq_eq_0

  -- Expand (x + z)^2 + (y - t)^2 and simplify using known values and derived equality
  have h_sum_sq_eq_13 : (x + z)^2 + (y - t)^2 = 13 := by
    have h_expand : (x + z)^2 + (y - t)^2 = (x^2 + y^2) + (z^2 + t^2) + 2*(x*z - y*t) := by
      ring
    rw [h_expand, h₁, h₂, h_xz_eq_yt]
    norm_num

  -- Prove that (x + z)^2 ≤ 13 by leveraging the non-negativity of (y - t)^2
  have h_le_13 : (x + z)^2 ≤ 13 := by
    linarith [h_sum_sq_eq_13, sq_nonneg (y - t)]

  -- Establish the absolute bound |x + z| ≤ Real.sqrt 13 using the previous result
  have h_abs_le_sqrt : |x + z| ≤ Real.sqrt 13 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x + z), Real.sqrt_nonneg 13, Real.mul_self_sqrt (show 0 ≤ 13 by norm_num)]
    · nlinarith [sq_nonneg (x + z), Real.sqrt_nonneg 13, Real.mul_self_sqrt (show 0 ≤ 13 by norm_num)]
  -- Decompose the absolute bound into the final inequality x + z ≤ Real.sqrt 13
  have h_abs_le_sqrt_decomp : -Real.sqrt 13 ≤ x + z ∧ x + z ≤ Real.sqrt 13 := by
    exact abs_le.mp h_abs_le_sqrt
  have h_right : x + z ≤ Real.sqrt 13 := h_abs_le_sqrt_decomp.2
  exact h_right