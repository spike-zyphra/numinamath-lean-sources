import Mathlib

open Real

theorem algebra_318173 {f : ℝ → ℝ} (hf : f = fun x => x + 2 / x) :
    IsLeast {x | ∃ P : ℝ × ℝ, P.1 > 0 ∧ P.2 = f P.1 ∧ x = abs (P.1 - 0) + abs (P.2 - 0)} 4 := by
  constructor
  · -- Show 4 is in the set.
    use (1, 3)
    constructor
    · norm_num
    constructor
    · -- Show that 3 = f(1)
      rw [hf]
      norm_num
    · -- Show that 4 = |1| + |3|
      norm_num [abs]
  · -- Show 4 is a lower bound
    intro s hs
    rcases hs with ⟨P, hP1, hP2, hP3⟩
    have h1 : P.1 > 0 := hP1
    have h2 : P.2 = f P.1 := hP2
    have h3 : s = abs (P.1 - 0) + abs (P.2 - 0) := hP3
    have h4 : f = fun x => x + 2 / x := by
      exact hf
    have hP2' : P.2 = P.1 + 2 / P.1 := by
      rw [h2, h4]
    have h5 : abs (P.1 - 0) = P.1 := by
      have h6 : P.1 - 0 ≥ 0 := by linarith
      rw [abs_of_nonneg h6]
      all_goals linarith
    have h6 : P.2 > 0 := by
      rw [hP2']
      have h7 : P.1 > 0 := h1
      have h8 : 2 / P.1 > 0 := by
        apply div_pos
        norm_num
        all_goals linarith
      have h9 : P.1 + 2 / P.1 > 0 := by linarith
      exact h9
    have h7 : abs (P.2 - 0) = P.2 := by
      rw [show P.2 - 0 = P.2 by ring]
      rw [abs_of_pos h6]
    rw [h5, h7] at h3
    have h8 : s = 2 * P.1 + 2 / P.1 := by
      rw [h3]
      linarith [hP2']
    have h9 : 2 * P.1 + 2 / P.1 ≥ 4 := by
      have h11 : P.1 > 0 := h1
      have h12 : 2 * P.1 + 2 / P.1 - 4 ≥ 0 := by
        have h13 : 2 * P.1 + 2 / P.1 - 4 = 2 * (P.1 + 1 / P.1 - 2) := by
          field_simp
          <;> ring
        rw [h13]
        have h14 : P.1 + 1 / P.1 ≥ 2 := by
          have h15 : P.1 + 1 / P.1 - 2 ≥ 0 := by
            have h16 : P.1 + 1 / P.1 - 2 = (P.1 - 1) ^ 2 / P.1 := by
              field_simp
              <;> ring
            rw [h16]
            have h17 : P.1 > 0 := h1
            have h18 : (P.1 - 1) ^ 2 ≥ 0 := sq_nonneg (P.1 - 1)
            have h19 : (P.1 - 1) ^ 2 / P.1 ≥ 0 := by
              apply div_nonneg
              linarith
              all_goals linarith
            linarith
          linarith
        have h15 : P.1 + 1 / P.1 - 2 ≥ 0 := by linarith
        nlinarith
      nlinarith
    linarith [h8, h9]