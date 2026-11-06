import Mathlib

theorem algebra_298506 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a * b * c = 8) :
    c < 0 ∨ c ≥ 2 * 4 ^ ((1 : ℝ) / 3) := by
  by_cases hc : c < 0
  · -- If c < 0, then the first condition holds
    left
    exact hc
  · -- If c ≥ 0, we need to prove the second condition.
    have h₂ : c ≥ 0 := by linarith
    by_cases hc2 : c > 0
    · -- Assume c > 0.
      have h3 : a + b = -c := by linarith
      have h4 : a * b = 8 / c := by
        have hc2' : c ≠ 0 := by linarith
        field_simp [hc2']
        nlinarith
      have h5 : (a - b) ^ 2 = c ^ 2 - 32 / c := by
        have ha : a + b = -c := h3
        have hb : a * b = 8 / c := h4
        have ha1 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by
          nlinarith
        rw [ha1, ha, hb]
        field_simp [show c ≠ 0 by linarith]
        <;> ring
        all_goals nlinarith
      have h6 : c ^ 2 - 32 / c ≥ 0 := by
        have h7 : (a - b) ^ 2 ≥ 0 := by nlinarith
        have h8 : (a - b) ^ 2 = c ^ 2 - 32 / c := by linarith [h5]
        linarith [h8, h7]
      have h7 : c ≥ 2 * 4 ^ ((1 : ℝ) / 3) := by
        have h8 : c ^ 3 ≥ 32 := by
          have h7 : c ^ 2 - 32 / c ≥ 0 := h6
          have hc2' : c > 0 := hc2
          have h8 : c ^ 3 ≥ 32 := by
            have h9 : c ^ 2 * c - 32 ≥ 0 := by
              have h9 : c ^ 2 - 32 / c ≥ 0 := h7
              have hc2' : c > 0 := hc2
              have : c ^ 2 * c - 32 = c * (c ^ 2 - 32 / c) := by
                field_simp [show c ≠ 0 by linarith]
                <;> ring
              nlinarith [show c > 0 by linarith, h9, h7]
            linarith
          linarith
        have h10 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 32 := by
          calc
            (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 8 * ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by ring_nf
            _ = 8 * ((4 : ℝ) ^ (1 / 3 * (3 : ℝ))) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              ring_nf
              all_goals linarith
            _ = 8 * (4 : ℝ) ^ (1 : ℝ) := by
              norm_num
              all_goals linarith
            _ = 8 * (4 : ℝ) := by
              simp
            _ = 32 := by norm_num
        have h11 : c ^ 3 ≥ (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
          linarith [h8, h10]
        have h12 : c ≥ 2 * (4 : ℝ) ^ ((1 : ℝ) / 3) := by
          have h13 : (c) ^ 3 ≥ (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := h11
          have h14 : c ≥ 0 := by linarith
          have h15 : 2 * (4 : ℝ) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
          have h16 : c ≥ 2 * (4 : ℝ) ^ ((1 : ℝ) / 3) := by
            nlinarith [sq_nonneg (c ^ 2 - (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg (c ^ 2 + (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg (c - 2 * (4 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (c + 2 * (4 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (c ^ 2 - (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg (c ^ 2 + (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2)]
          linarith
        linarith
      right
      linarith
    · -- So c = 0, which is a contradiction with h₁
      have hc0 : c = 0 := by nlinarith
      rw [hc0] at h₁
      nlinarith