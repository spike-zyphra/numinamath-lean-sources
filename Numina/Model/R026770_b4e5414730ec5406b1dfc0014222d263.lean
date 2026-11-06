import Mathlib

theorem algebra_310235 {x y z : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hz : 2 ≤ z)
    (h : Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2) = (x + y + z) / 2) :
    x = 1 ∧ y = 2 ∧ z = 3 := by

  have h10 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  have h11 : (Real.sqrt (y - 1)) ^ 2 = y - 1 := by
    rw [Real.sq_sqrt]
    have h' : 0 ≤ y - 1 := by linarith
    linarith
  have h12 : (Real.sqrt (z - 2)) ^ 2 = z - 2 := by
    rw [Real.sq_sqrt]
    have h' : 0 ≤ z - 2 := by linarith
    linarith

  have h7 : (Real.sqrt x) ^ 2 + (Real.sqrt (y - 1)) ^ 2 + (Real.sqrt (z - 2)) ^ 2 + 3 =
    2 * (Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2)) := by
    nlinarith [h, h10, h11, h12]

  have h8 : (Real.sqrt x - 1) ^ 2 + (Real.sqrt (y - 1) - 1) ^ 2 + (Real.sqrt (z - 2) - 1) ^ 2 = 0 := by
    nlinarith

  have h8a : (Real.sqrt x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1)]
  have h8b : (Real.sqrt (y - 1) - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1)]
  have h8c : (Real.sqrt (z - 2) - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1)]

  have h9a : Real.sqrt x - 1 = 0 := by
    rwa [sq_eq_zero_iff] at h8a
  have h9b : Real.sqrt (y - 1) - 1 = 0 := by
    rwa [sq_eq_zero_iff] at h8b
  have h9c : Real.sqrt (z - 2) - 1 = 0 := by
    rwa [sq_eq_zero_iff] at h8c

  have hx1 : Real.sqrt x = 1 := by linarith
  have hy1 : Real.sqrt (y - 1) = 1 := by linarith
  have hz1 : Real.sqrt (z - 2) = 1 := by linarith

  have hx2 : x = 1 := by
    nlinarith [h10, hx1, Real.sqrt_nonneg x]

  have hy2 : y = 2 := by
    have eq1 : (Real.sqrt (y - 1)) ^ 2 = y - 1 := h11
    have eq2 : Real.sqrt (y - 1) = 1 := hy1
    nlinarith [Real.sqrt_nonneg (y - 1), sq_nonneg (Real.sqrt (y - 1) - 1), eq1, eq2]

  have hz2 : z = 3 := by
    have eq1 : (Real.sqrt (z - 2)) ^ 2 = z - 2 := h12
    have eq2 : Real.sqrt (z - 2) = 1 := hz1
    nlinarith [Real.sqrt_nonneg (z - 2), sq_nonneg (Real.sqrt (z - 2) - 1), eq1, eq2]

  exact ⟨hx2, hy2, hz2⟩