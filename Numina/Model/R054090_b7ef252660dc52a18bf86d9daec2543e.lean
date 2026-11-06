import Mathlib

theorem algebra_277282 {p : ℝ} (hp : p > 0) :
    IsGreatest {x | ∃ r : ℝ × ℝ, r.1 > 0 ∧ r.2 > 0 ∧ 2 * (r.1 + r.2) = p ∧ x = r.1 * r.2} (p ^ 2 / 16) := by
  constructor
  · -- Show that $p^2/16$ is achievable by some rectangle (the square)
    use (p / 4, p / 4)
    constructor
    · -- Show first side is positive
      linarith [hp]
    constructor
    · -- Show second side is positive
      linarith [hp]
    constructor
    · -- Show perimeter is p
      ring
    · -- Show area is p^2 / 16
      ring
  · -- Show that $p^2/16$ is indeed the greatest value
    intro x hx
    rcases hx with ⟨r, hr1, hr2, hr3, hx⟩
    have h1 : r.1 + r.2 = p / 2 := by
      linarith
    have h2 : r.1 * r.2 ≤ (p ^ 2) / 16 := by
      nlinarith [sq_nonneg (r.1 - r.2), sq_nonneg (r.1 + r.2 - p / 2)]
    linarith [hx, h2]