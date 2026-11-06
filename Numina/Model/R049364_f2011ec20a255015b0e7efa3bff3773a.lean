import Mathlib

theorem algebra_131439 (c : ℝ) :
    (∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x - y = 2 ∧ c * x + y = 3) ↔
    -1 < c ∧ c < 3 / 2 := by
  constructor
  · -- Forward direction: If there exists a solution in the first quadrant, then $-1 < c < \frac{3}{2}$.
    intro h
    obtain ⟨x, y, hx, hy, h1, h2⟩ := h
    have h3 : x = y + 2 := by linarith
    rw [h3] at h2
    have h4 : y = (3 - 2 * c) / (c + 1) := by
      have h5 : c + 1 ≠ 0 := by
        by_contra h6
        have h61 : c = -1 := by linarith
        have h7 : c * (y + 2) + y = 3 := by linarith
        rw [show c = -1 by linarith] at h7
        nlinarith
      field_simp [h5]
      <;> linarith
    have h5 : x = 5 / (c + 1) := by
      rw [h3]
      rw [h4]
      have h7 : c + 1 ≠ 0 := by
        by_contra h6
        have h61 : c = -1 := by linarith
        have h7 : c * (y + 2) + y = 3 := by linarith
        rw [show c = -1 by linarith] at h7
        nlinarith
      field_simp [h7]
      <;> linarith
    have h6 : c + 1 > 0 := by
      have h7 : 5 / (c + 1) > 0 := by linarith [hx, h5]
      apply div_pos_iff.mp at h7
      cases h7 with
      | inl h8 =>
        linarith
      | inr h8 =>
        nlinarith
    have h7 : 3 - 2 * c > 0 := by
      have h8 : (3 - 2 * c) / (c + 1) > 0 := by
        linarith [hy, h4]
      apply div_pos_iff.mp at h8
      cases h8 with
      | inl h9 =>
        have h91 : c + 1 > 0 := by linarith
        linarith
      | inr h9 =>
        have h92 : c + 1 < 0 := by linarith
        nlinarith
    constructor
    · -- Prove $c > -1$
      linarith
    · -- Prove $c < \frac{3}{2}$
      linarith
  · -- Backward direction: If $-1 < c < \frac{3}{2}$, then there exists a solution in the first quadrant.
    intro h
    obtain ⟨hc1, hc2⟩ := h
    have hc1' : c + 1 > 0 := by linarith
    have h3 : 3 - 2 * c > 0 := by linarith
    use 5 / (c + 1)
    use (3 - 2 * c) / (c + 1)
    constructor
    · -- Show that x > 0
      have h7 : c + 1 > 0 := hc1'
      apply div_pos
      norm_num
      all_goals linarith
    constructor
    · -- Show that y > 0
      have h7 : c + 1 > 0 := hc1'
      have h8 : 3 - 2 * c > 0 := by linarith
      apply div_pos
      linarith
      all_goals linarith
    constructor
    · -- Show that x - y = 2
      field_simp [(show c + 1 ≠ 0 by linarith)]
      <;> nlinarith
    · -- Show that c * x + y = 3
      field_simp [(show c + 1 ≠ 0 by linarith)]
      <;> nlinarith