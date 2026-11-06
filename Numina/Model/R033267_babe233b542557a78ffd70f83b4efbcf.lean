import Mathlib

theorem algebra_222084 :
    {(a, b) : ℝ × ℝ | ∀ x ∈ Set.Icc 0 1, |x^2 - a * x - b| ≤ 1 / 8} = {(1, -1 / 8)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume that for all x in [0, 1], |x^2 - a * x - b| ≤ 1 / 8|, prove that (a, b) = (1, -1/8).
    intro h
    have h1 : |(0:ℝ)^2 - a * (0:ℝ) - b| ≤ 1 / 8 := h 0 (by norm_num)
    have h2 : |(1:ℝ)^2 - a * (1:ℝ) - b| ≤ 1 / 8 := h 1 (by norm_num)
    have h3 : |(0.5:ℝ)^2 - a * (0.5:ℝ) - b| ≤ 1 / 8 := h 0.5 (by norm_num)
    have hb1 : -1 / 8 ≤ b := by
      cases' abs_le.mp h1 with h1_neg h1_pos
      linarith
    have hb2 : b ≤ 1 / 8 := by
      cases' abs_le.mp h1 with h1_neg h1_pos
      linarith
    have h4 : -1 / 8 ≤ (1:ℝ) - a - b := by
      cases' abs_le.mp h2 with h4 h4
      linarith
    have h5 : (1:ℝ) - a - b ≤ 1 / 8 := by
      cases' abs_le.mp h2 with h4 h4
      linarith
    have h6 : -1 / 8 ≤ (0.5:ℝ)^2 - a * (0.5:ℝ) - b := by
      cases' abs_le.mp h3 with h6 h6
      linarith
    have h7 : (0.5:ℝ)^2 - a * (0.5:ℝ) - b ≤ 1 / 8 := by
      cases' abs_le.mp h3 with h6 h6
      linarith
    have h8 : a = 1 := by
      ring_nf at h4 h5 h6 h7
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1 / 8)]
    have h9 : b = -1 / 8 := by
      rw [h8] at h4 h5
      linarith
    simp [h8, h9]
  · -- Show that (1, -1/8) satisfies the condition.
    rintro (⟨rfl, rfl⟩)
    intro x hx
    rcases hx with ⟨hx0, hx1
    ⟩
    have h2 : -1 / 8 ≤ x ^ 2 - (1:ℝ) * x - (-1 / 8) := by
      nlinarith [sq_nonneg (x - 0.5)]
    have h3 : x ^ 2 - (1:ℝ) * x - (-1 / 8) ≤ 1 / 8 := by
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 1)]
    apply abs_le.mpr
    constructor <;> linarith [h2, h3]