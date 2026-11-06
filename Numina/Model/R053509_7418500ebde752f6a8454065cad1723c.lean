import Mathlib

theorem algebra_303646 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : ∀ x, f x = a * x - b * x ^ 2)
    (h : ∀ x, f x ≤ 1) :
    a ≤ 2 * Real.sqrt b := by
  have h1 : f (a / (2 * b)) ≤ 1 := by
    apply h
  have h2 : f (a / (2 * b)) = a^2 / (4 * b) := by
    rw [hf]
    field_simp
    ring
  rw [h2] at h1
  have h4 : a^2 ≤ 4 * b := by
    have h5 : a^2 / (4 * b) ≤ 1 := by linarith
    have h6 : a^2 ≤ 4 * b := by
      have h7 : 0 < 4 * b := by nlinarith
      have h8 : a^2 ≤ 4 * b := by
        apply (div_le_iff (by nlinarith)).mp at h5
        linarith
      linarith
    linarith
  have h6 : Real.sqrt (4 * b) = 2 * Real.sqrt b := by
    have h7 : Real.sqrt (4 * b) = Real.sqrt (4 * b) := rfl
    calc 
      Real.sqrt (4 * b) = Real.sqrt (4 * b) := by rfl
      _ = Real.sqrt ((2 : ℝ) ^ 2 * b) := by ring_nf
      _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt b := by
        rw [Real.sqrt_mul (by nlinarith)]
      _ = (2 : ℝ) * Real.sqrt b := by
        rw [Real.sqrt_sq (by norm_num)]
        all_goals norm_num
      _ = 2 * Real.sqrt b := by ring
  have h58 : a ≤ 2 * Real.sqrt b := by
    have h5 : a^2 ≤ 4 * b := h4
    have h50 : Real.sqrt (4 * b) = 2 * Real.sqrt b := h6
    have h57 : Real.sqrt b > 0 := Real.sqrt_pos.mpr hb
    have h58 : a ≤ Real.sqrt (4 * b) := by
      nlinarith [Real.sqrt_nonneg (4 * b), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 4 * b by nlinarith), sq_nonneg (a - Real.sqrt (4 * b)), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * b by nlinarith), sq_nonneg (a), mul_pos ha hb]
    rw [h50] at h58
    linarith
  exact h58
  all_goals linarith