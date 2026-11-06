import Mathlib

theorem algebra_328106 (a b : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x - b * x ^ 2)
    (h1 : b > 0) (h2 : ∀ x, f x ≤ 1) :
    a ≤ 2 * Real.sqrt b := by
  have h3 : f (a / (2 * b)) ≤ 1 := h2 (a / (2 * b))
  have h4 : f (a / (2 * b)) = a ^ 2 / (4 * b) := by 
    rw [hf]
    field_simp
    <;> ring_nf <;> field_simp <;> ring
  have h5 : a ^ 2 ≤ 4 * b := by
    rw [h4] at h3
    have h6 : 0 < 4 * b := by linarith
    have h7 : a ^ 2 / (4 * b) ≤ (1 : ℝ) := by linarith
    have h8 : a ^ 2 ≤ (1 : ℝ) * (4 * b) := by
      have h9 : 0 < 4 * b := by linarith
      apply (div_le_iff₀' h9).mp at h7
      linarith
    linarith
  have h6 : Real.sqrt b > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h7 : a ≤ 2 * Real.sqrt b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), h5, Real.sqrt_pos.mpr h1, sq_pos_of_pos ha]
  linarith [h7]