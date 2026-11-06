import Mathlib

theorem algebra_271252 (s : ℝ) :
    (∀ t : ℝ, ∃ x : ℝ, s * x ^ 2 + t * x + s - 1 = 0) ↔
    0 < s ∧ s ≤ 1 := by
  constructor
  · -- Assume the equation has real roots for any real t, prove 0 < s ∧ s ≤ 1
    intro h
    have h1 := h 0
    rcases h1 with ⟨x1, h1⟩
    have h2 : s > 0 := by
      nlinarith [sq_nonneg (x1)]
    have h3 : ∀ t : ℝ, t ^ 2 - 4 * s * (s - 1) ≥ 0 := by
      intro t
      have h4 := h t
      rcases h4 with ⟨x, hx⟩
      nlinarith [sq_nonneg (s * x + t / 2), sq_nonneg (x + t / (2 * s)), sq_nonneg (x), sq_nonneg (s * x + t / 2)]
    have h4 : s * (s - 1) ≤ 0 := by
      have h5 := h3 0
      nlinarith
    constructor
    · linarith
    · nlinarith
  · -- Assume 0 < s ∧ s ≤ 1, prove ∀ t : ℝ, ∃ x : ℝ, s * x ^ 2 + t * x + s - 1 = 0
    rintro ⟨hs_pos, hs_le_one⟩
    intro t
    have h1 : t ^ 2 - 4 * s * (s - 1) ≥ 0 := by
      nlinarith [sq_nonneg (t), sq_nonneg (s - 1)]
    use (-t + Real.sqrt (t^2 - 4 * s * (s - 1))) / (2 * s)
    field_simp
    nlinarith [Real.sqrt_nonneg (t^2 - 4 * s * (s - 1)), Real.sq_sqrt (show (t^2 - 4 * s * (s - 1)) ≥ 0 by nlinarith)]