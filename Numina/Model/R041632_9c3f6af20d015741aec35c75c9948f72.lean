import Mathlib

theorem algebra_228452 :
    { (x, y) : ℝ × ℝ | x^2 - x * y + y^2 ≠ 0 ∧ x^3 + y^3 = 2 ∧ (x^2 + x * y + y^2) / (x^2 - x * y + y^2) = 3 } = {(1, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is in the set, need to prove (x, y) = (1, 1)
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : x ^ 2 + x * y + y ^ 2 = 3 * (x ^ 2 - x * y + y ^ 2) := by
      have h5 : x ^ 2 - x * y + y ^ 2 ≠ 0 := h₁
      field_simp [h5] at h₃
      linarith
    have h5 : (x - y) ^ 2 = 0 := by
      nlinarith
    have h6 : x = y := by
      nlinarith
    have h7 : x ^ 3 + y ^ 3 = 2 := h₂
    rw [show y = x by linarith [h6] ] at h7
    have h8 : x ^ 3 = 1 := by
      nlinarith
    have h9 : x = 1 := by
      have h10 : x ^ 3 - 1 = 0 := by linarith
      have h11 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
        ring_nf at h10 ⊢
        linarith
      cases' (mul_eq_zero.1 h11) with h12 h13
      · -- x - 1 = 0
        linarith
      · -- x^2 + x + 1 = 0
        have h14 : x ^ 2 + x + 1 > 0 := by
          nlinarith [sq_nonneg (x + 1 / 2)]
        have h15 : x ^ 2 + x + 1 = 0 := by linarith
        linarith [h14, h15]
    have h10 : y = 1 := by
      linarith [h6, h9]
    simp [h9, h10]
  · -- Assume (x, y) = (1, 1), need to prove it's in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Show 1^2 - 1 * 1 + 1^2 ≠ 0
      norm_num
    constructor
    · -- Show 1^3 + 1^3 = 2
      norm_num
    · -- Show (1^2 + 1 * 1 + 1^2) / (1^2 - 1 * 1 + 1^2) = 3
      norm_num