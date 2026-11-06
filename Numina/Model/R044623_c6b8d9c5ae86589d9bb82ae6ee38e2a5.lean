import Mathlib

theorem algebra_155544 {x y z : ℝ}
(h₀ : x > 0)
(h₁ : y > 0)
(h₂ : z > 0)
(hx : x = 1 + Real.log y)
(hy : y = 1 + Real.log z)
(hz : z = 1 + Real.log x) :
x = 1 ∧ y = 1 ∧ z = 1 := by

  have h4 : ∀ t : ℝ, t > 0 → t ≥ 1 + Real.log t := by
    intro t ht
    have h5 : Real.log t ≤ t - 1 := by
      linarith [Real.log_le_sub_one_of_pos ht]
    linarith

  have h5 : y ≥ x := by
    have h6 : y ≥ 1 + Real.log y := by
      have h7 : y > 0 := h₁
      have h8 := h4 y h7
      linarith
    have h9 : x = 1 + Real.log y := by
      linarith [hx]
    linarith [h9, h6]

  have h8 : z ≥ y := by
    have h9 : z ≥ 1 + Real.log z := by
      have h10 : z > 0 := h₂
      have h11 := h4 z h10
      linarith
    have h10 : y = 1 + Real.log z := by
      linarith [hy]
    linarith [h10, h9]

  have h10 : x ≥ z := by
    have h11 : x ≥ 1 + Real.log x := by
      have h12 : x > 0 := h₀
      have h13 := h4 x h12
      linarith
    have h13 : z = 1 + Real.log x := by
      linarith [hz]
    linarith [h13, h11]

  have h14 : y = x := by
    linarith [h5, h8, h10]

  have h15 : z = x := by
    linarith [h14, h8, h10]

  have h16 : x = 1 := by
    have h17 : x = 1 + Real.log y := by
      linarith [hx]
    rw [show y = x by linarith [h14]] at h17
    by_cases h20 : x > 1
    · -- Assume x > 1
      have h21 : Real.log x < x - 1 := by
        have h22 : Real.log x < x - 1 := by
          linarith [Real.log_lt_sub_one_of_pos (show x > 0 by linarith) (by linarith)]
        linarith
      nlinarith [h17, h21]
    by_cases h21 : x < 1
    · -- Assume x < 1
      have h20 : Real.log x < x - 1 := by
        have h22 : Real.log x < x - 1 := by
          linarith [Real.log_lt_sub_one_of_pos (show x > 0 by linarith) (by linarith)]
        linarith
      nlinarith [h17, h20]
    linarith

  have h17 : y = 1 := by
    nlinarith [h14, h16]

  have h18 : z = 1 := by
    nlinarith [h15, h16]

  exact ⟨h16, h17, h18⟩