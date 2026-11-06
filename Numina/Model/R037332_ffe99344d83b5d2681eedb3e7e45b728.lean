import Mathlib

open Real

theorem inequalities_116663 :
    IsGreatest {x : ℝ | ∃ a b c, 0 < a ∧ a ≤ b ∧ b ≤ a + b ∧ a + b ≤ c ∧ x = a / b + b / c} (3 / 2) := by
  constructor
  · -- Show 3/2 is in the set.
    use 1, 1, 2
    norm_num
  · -- Show 3/2 is the greatest.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hab, hb, hc, hx⟩
    have h1 : 0 < a := ha
    have h2 : a ≤ b := hab
    have h3 : b ≤ a + b := hb
    have h4 : a + b ≤ c := hc
    have h5 : x = a / b + b / c := hx
    have hb1 : 0 < b := by
      linarith
    have hc1 : a + b ≤ c := h4
    have hc2 : 0 < c := by
      nlinarith
    have h6 : a / b + b / c ≤ (3 / 2 : ℝ) := by
      have h7 : a + b ≤ c := hc1
      have h8 : (b / c) ≤ (b / (a + b)) := by
        apply (div_le_div_iff (by linarith) (by linarith)).mpr
        nlinarith
      have h14 : a / b + b / (a + b) ≤ (3 / 2 : ℝ) := by
        have hb1 : 0 < b := hb1
        have h5 : 0 < (a + b : ℝ) := by
          linarith
        have hx1 : a / b + b / (a + b) - (3 / 2 : ℝ) ≤ 0 := by
          have hx2 : a / b + b / (a + b) - (3 / 2 : ℝ) = (2 * a * (a + b) + 2 * b ^ 2 - 3 * b * (a + b)) / (2 * b * (a + b)) := by
            field_simp
            ring
          rw [hx2] at *
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show numerator is nonpositive
            nlinarith [sq_nonneg (a - b : ℝ), sq_nonneg (a * 2 - b : ℝ)]
          · -- Show denominator is nonnegative
            positivity
        linarith
      have h5 : a / b + b / c ≤ a / b + b / (a + b) := by
        have h8' : b / c ≤ b / (a + b) := h8
        linarith
      linarith [h14, h5]
    have hx1 : x ≤ (3 / 2 : ℝ) := by
      linarith [h6, h5]
    linarith