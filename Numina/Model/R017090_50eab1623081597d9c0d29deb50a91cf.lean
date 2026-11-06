import Mathlib

theorem algebra_221564 (k : ℝ) :
    (k < -3 ∨ k > 1 / 6) ↔
    ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 2 * x + 7 * y = 14 ∧ k * x - y = k + 1 := by 
  constructor 
  · -- Assume (k < -3 ∨ k > 1 / 6), prove ∃ x y, x>0 ∧ y>0 ∧ 2x + 7y = 14 ∧ kx - y = k + 1
    rintro (h | h)
    · -- k < -3
      have H1 : k < -3 := h 
      have hk1 : 2 + 7 * k < 0 := by linarith
      have hk2 : 7 * k + 21 < 0 := by linarith
      use (7 * k + 21) / (2 + 7 * k), (12 * k - 2) / (2 + 7 * k)
      constructor
      · -- Show x > 0
        apply div_pos_of_neg_of_neg
        · -- Show 7k + 21 < 0
          linarith 
        · -- Show 2 + 7k < 0
          linarith 
      constructor 
      · -- Show y > 0 
        apply div_pos_of_neg_of_neg
        · -- Show 12k - 2 < 0
          linarith 
        · -- Show 2 + 7k < 0 
          linarith 
      constructor 
      · -- Show 2 * x + 7 * y = 14 
        field_simp [(show (2 + 7 * k : ℝ) ≠ 0 by 
          linarith 
        )]
        <;> ring 
      · -- Show k * x - y = k + 1 
        field_simp [(show (2 + 7 * k : ℝ) ≠ 0 by 
          linarith 
        )]
        <;> ring_nf <;> linarith 
    · -- k > 1/6 
      have H2 : k > 1 / 6 := h 
      have hk1 : 2 + 7 * k > 0 := by linarith 
      have hk2 : 7 * k + 21 > 0 := by linarith 
      use (7 * k + 21) / (2 + 7 * k), (12 * k - 2) / (2 + 7 * k)
      constructor 
      · -- Show x > 0 
        apply div_pos 
        · -- Show 7k + 21 > 0 
          linarith 
        · -- Show 2 + 7k > 0 
          linarith 
      constructor 
      · -- Show y > 0 
        have hk3 : 12 * k - 2 > 0 := by linarith 
        apply div_pos 
        · -- Show 12k - 2 > 0 
          linarith 
        · -- Show 2 + 7k > 0 
          linarith 
      constructor 
      · -- Show 2 * x + 7 * y = 14 
        field_simp [(show (2 + 7 * k : ℝ) ≠ 0 by 
          linarith 
        )]
        <;> ring 
      · -- Show k * x - y = k + 1 
        field_simp [(show (2 + 7 * k : ℝ) ≠ 0 by 
          linarith 
        )]
        <;> ring_nf <;> linarith 
  · -- Assume ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 2 * x + 7 * y = 14 ∧ k * x - y = k + 1, prove k < -3 ∨ k > 1 / 6 
    rintro ⟨x, y, hx, hy, heq1, heq2⟩ 
    by_contra h 
    push_neg at h 
    have h1 : -3 ≤ k := by linarith 
    have h2 : k ≤ 1 / 6 := by linarith 
    nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 2), 
      sq_nonneg (k + 3), sq_nonneg (k - 1 / 6), 
      mul_pos hx hy, 
      mul_pos hx (show 0 < (14 - 2 * x) / 7 by linarith)
    ]