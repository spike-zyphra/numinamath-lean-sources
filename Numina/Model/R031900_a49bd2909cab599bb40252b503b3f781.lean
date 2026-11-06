import Mathlib

theorem algebra_265305 (x y z : ℝ) :
    x ^ 4 + y ^ 2 + 4 = 5 * y * z ∧ y ^ 4 + z ^ 2 + 4 = 5 * z * x ∧ z ^ 4 + x ^ 2 + 4 = 5 * x * y ↔
    (x = Real.sqrt 2 ∧ y = Real.sqrt 2 ∧ z = Real.sqrt 2) ∨
    (x = -Real.sqrt 2 ∧ y = -Real.sqrt 2 ∧ z = -Real.sqrt 2) := by
  constructor
  · -- Assume the system of equations is satisfied, prove the solutions
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^ 2 - 2), sq_nonneg (z ^ 2 - 2),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - Real.sqrt 2), sq_nonneg (x + Real.sqrt 2),
        sq_nonneg (y - Real.sqrt 2), sq_nonneg (y + Real.sqrt 2),
        sq_nonneg (z - Real.sqrt 2), sq_nonneg (z + Real.sqrt 2),
        Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
    have h5 : x - y = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have h6 : y - z = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have h8 : x = y := by
      linarith
    have h9 : y = z := by
      linarith
    have h11 : x ^ 2 = 2 := by
      have h_eq1 := h₁
      rw [show y = x by linarith [h8]] at h_eq1
      rw [show z = x by linarith [h8, h9]] at h_eq1
      nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x + Real.sqrt 2), sq_nonneg (x - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
    have hx1 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
      have h100 : x ^ 2 = 2 := h11
      have h101 : x ^ 2 - (2 : ℝ) = 0 := by linarith
      have h102 : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
      cases (mul_eq_zero.mp h102) with
      | inl h103 =>
        left
        linarith
      | inr h104 =>
        right
        linarith
    cases hx1 with
    | inl hx2 =>
      left
      constructor
      · exact hx2
      constructor
      · rw [show y = x by linarith [h8]]
        exact hx2
      · rw [show z = x by linarith [h8, h9]]
        exact hx2
    | inr hx3 =>
      right
      constructor
      · exact hx3
      constructor
      · rw [show y = x by linarith [h8]]
        exact hx3
      · rw [show z = x by linarith [h8, h9]]
        exact hx3
  · -- Show that the solutions satisfy the system
    rintro (h | h)
    · -- Case (√2, √2, √2)
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- First equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]
      constructor
      · -- Second equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]
      · -- Third equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]
    · -- Case (-√2, -√2, -√2)
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- First equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]
      constructor
      · -- Second equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]
      · -- Third equation
        rw [hx, hy, hz]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), Real.sqrt_nonneg 2]