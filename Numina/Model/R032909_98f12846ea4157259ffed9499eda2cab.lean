import Mathlib

theorem algebra_19409 (h : ℝ → ℝ) (h_def : h = fun t => -25*t^2 + 75*t + 24) :
    IsMaxOn h (Set.Ici 0) (3 / 2) := by
  unfold IsMaxOn
  intro x hx
  have h1 : x ≥ 0 := by
    simpa using hx
  simp [h_def]
  have h2 : -25 * (3 / 2) ^ 2 + 75 * (3 / 2) + 24 ≥ -25 * x ^ 2 + 75 * x + 24 := by
    have h3 : -25 * (x - 3 / 2) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    nlinarith [sq_nonneg (x - 3 / 2), h3]
  linarith