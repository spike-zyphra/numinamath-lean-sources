import Mathlib

theorem inequalities_327831 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : 2 * a + 2 * b ≤ 15) (h₂ : 4 / a + 3 / b ≤ 2) :
    3 * a + 4 * b ∈ Set.Icc 24 27 := by

  have h3 : 0 < a * b := mul_pos ha hb
  have h4 : 4 * b + 3 * a ≤ 2 * (a * b) := by
    have h4 : 0 < a := ha
    have h5 : 0 < b := hb
    have h6 : 4 / a + 3 / b ≤ 2 := h₂
    have h7 : 4 / a + 3 / b = (4 * b + 3 * a) / (a * b) := by
      field_simp
      <;> ring
    rw [h7] at h6
    have h8 : (4 * b + 3 * a) / (a * b) ≤ 2 := h6
    have h9 : 0 < a * b := by positivity
    have h10 : 4 * b + 3 * a ≤ 2 * (a * b) := by
      apply (div_le_iff₀ h9).mp at h8
      linarith
    linarith

  constructor
  · -- Show 24 ≤ 3 * a + 4 * b
    have h5 : 24 ≤ 3 * a + 4 * b := by
      nlinarith [mul_pos ha hb, sq_nonneg (a - 2), sq_nonneg (b - 3 / 2), 
        sq_nonneg (3 * a - 4 * b), sq_nonneg (a - b), 
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
      ]
    linarith
  · -- Show 3 * a + 4 * b ≤ 27
    have h6 : 3 * a + 4 * b ≤ 27 := by
      nlinarith [mul_pos ha hb, sq_nonneg (a - 3), sq_nonneg (b - 3 / 2), 
        sq_nonneg (3 * a - 4 * b), sq_nonneg (a - b), 
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
      ]
    linarith