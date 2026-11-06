import Mathlib

theorem algebra_21149 :
    {(a, b) : ℝ × ℝ | a ^ 2 + a * a + b = 0 ∧ b ^ 2 + a * b + b = 0} = {(0,0), (1,-2), (-1/2,-1/2)} := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- Assume both equations are satisfied
    rintro ⟨h1, h2⟩
    have h3 : b = -2 * a ^ 2 := by
      ring_nf at h1 ⊢
      linarith
    rw [h3] at h2
    have h4 : 2 * a ^ 2 * (2 * a ^ 2 - a - 1) = 0 := by
      ring_nf at h2 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case 2 * a ^ 2 = 0
      have ha : a = 0 := by
        nlinarith
      have hb : b = 0 := by
        rw [ha] at h3
        linarith
      left
      simp [ha, hb]
    · -- Case 2 * a ^ 2 - a - 1 = 0
      have h7 : (a - 1) * (2 * a + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case a - 1 = 0
        have ha : a = 1 := by linarith
        have hb : b = -2 := by
          rw [ha] at h3
          linarith
        right
        left
        simp [ha, hb]
      · -- Case 2 * a + 1 = 0
        have ha : a = -1 / 2 := by linarith
        have hb : b = -1 / 2 := by
          rw [ha] at h3
          nlinarith
        right
        right
        simp [ha, hb]
  · -- Now the reverse direction
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0,0)
      constructor
      · norm_num
      · norm_num
    · -- (1, -2)
      constructor
      · norm_num
      · norm_num
    · -- (-1/2, -1/2)
      constructor
      · norm_num
      · norm_num