import Mathlib

theorem algebra_9372 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
(h : ∀ x, m * x + n > 0 ↔ 2 / 5 < x) :
∀ x, n * x - m < 0 ↔ -5 / 2 < x := by
  have h1 : m > 0 := by
    have h2 := h (2 / 5)
    norm_num at h2
    have h3 := h (3 / 5)
    norm_num at h3
    nlinarith
  have h2 : m * (2 / 5) + n = 0 := by
    have h10 := h (2 / 5)
    norm_num at h10
    have h30 : m * (2 / 5) + n ≤ 0 := by
      linarith
    have h40 : m * (2 / 5) + n ≥ 0 := by
      by_contra h4
      push_neg at h4
      have h5 : ∃ ε : ℝ, ε > 0 ∧ m * (2 / 5 + ε) + n ≤ 0 := by
        use (- (m * (2 / 5) + n) / m)
        constructor
        · -- Show ε > 0
          have h8 : m > 0 := h1
          apply div_pos
          · -- Show - (m * (2 / 5) + n) > 0
            nlinarith
          · -- Show m > 0
            linarith
        · -- Show m * (2 / 5 + ε) + n ≤ 0
          have h8 : m > 0 := h1
          have h10 : m * (2 / 5 + (- (m * (2 / 5) + n) / m)) + n = 0 := by
            field_simp [show m ≠ 0 by exact hm]
            <;> nlinarith
          nlinarith
      rcases h5 with ⟨ ε, hε, h13 ⟩
      have h14 : m * (2 / 5 + ε) + n > 0 := by
        have h15 : 2 / 5 < (2 / 5 + ε : ℝ) := by linarith
        have := h (2 / 5 + ε)
        have h18 := (this).mpr (by linarith)
        linarith
      linarith
    linarith
  intro x
  have h3 : n = -2 / 5 * m := by
    linarith
  constructor
  · -- Assume n * x - m < 0, prove -5/2 < x
    intro h5
    rw [h3] at h5
    have h6 : m > 0 := h1
    nlinarith
  · -- Assume -5/2 < x, prove n * x - m < 0
    intro h7
    rw [h3]
    have h6 : m > 0 := h1
    nlinarith