import Mathlib
open Real Set

theorem algebra_9363 {x : ℝ} (hx : x ∈ Ioo 0 π) :
    2 * cos (x - π / 4) = √2 ↔ x = π / 2 := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Assume 2 * cos (x - π / 4) = √2, prove x = π / 2
    intro h
    have h1 : cos (x - π / 4) = Real.sqrt 2 / 2 := by
      linarith
    have h2 : x - π / 4 = Real.pi / 4 ∨ x - π / 4 = - (Real.pi / 4) := by
      have h3 : cos (x - π / 4) = Real.sqrt 2 / 2 := h1
      have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      have h5 : cos (x - π / 4) = cos (Real.pi / 4) := by
        rw [h3, h4]
      by_cases h7 : x - π / 4 ≥ 0
      · -- x - π / 4 ≥ 0
        have h8 : x - π / 4 ≤ Real.pi := by
          linarith [Real.pi_pos, hx2]
        have h9 : x - π / 4 = Real.pi / 4 := by
          apply Real.injOn_cos
          · -- Show that x - π / 4 is in [0, π]
            constructor
            · linarith
            · linarith
          · -- Show that π / 4 is in [0, π]
            constructor
            · linarith [Real.pi_pos]
            · linarith [Real.pi_pos]
          · -- Show that cos (x - π / 4) = cos (π / 4)
            exact h5
        left
        linarith
      · -- x - π / 4 < 0
        have h8 : x - π / 4 ≥ - Real.pi / 4 := by
          linarith [show x ≥ 0 by linarith, Real.pi_pos]
        have h9 : x - π / 4 = - (Real.pi / 4) := by
          have h10 : x - π / 4 ≥ - Real.pi / 4 := h8
          have h11 : x - π / 4 < (0 : ℝ) := by
            linarith [Real.pi_pos]
          have h12 : cos (x - π / 4) = cos (Real.pi / 4) := h5
          have h13 : cos (x - π / 4) = cos (- (x - π / 4)) := by
            rw [show - (x - π / 4) = - (x - π / 4) by ring]
            rw [cos_neg]
          have h14 : cos (- (x - π / 4)) = cos (Real.pi / 4) := by
            linarith [h12, h13]
          have h15 : - (x - π / 4) = Real.pi / 4 := by
            apply Real.injOn_cos
            · -- Show - (x - π / 4) ∈ [0, π]
              constructor
              · linarith [show x ≥ 0 by linarith, Real.pi_pos]
              · linarith [Real.pi_pos, show x - π / 4 ≥ - Real.pi / 4 by linarith]
            · -- Show π / 4 ∈ [0, π]
              constructor
              · linarith [Real.pi_pos]
              · linarith [Real.pi_pos]
            · -- Show cos (- (x - π / 4)) = cos (π / 4)
              linarith [h14, show cos (Real.pi / 4) = Real.sqrt 2 / 2 by rw [cos_pi_div_four]]
          linarith
        right
        linarith
    cases h2 with
    | inl h3 =>
      linarith
    | inr h3 =>
      have h4 : x = 0 := by
        linarith
      linarith
  · -- Assume x = π / 2, prove 2 * cos (x - π / 4) = √2
    intro h
    rw [h]
    have h1 : cos ( (Real.pi / 2 : ℝ ) - Real.pi / 4 ) = Real.sqrt 2 / 2 := by
      have h2 : (Real.pi / 2 : ℝ ) - Real.pi / 4 = Real.pi / 4 := by
        linarith
      rw [h2]
      rw [cos_pi_div_four]
    linarith [h1]