import Mathlib

open Real Set

theorem algebra_305973 {x y : ℝ} (P Q : Set ℝ)
    (hP : P = {s | ∃ x : ℝ, s = x ^ 2 + 3 * x + 1})
    (hQ : Q = {t | ∃ y : ℝ, t = y ^ 2 - 3 * y + 1}) :
    P = Q := by
  rw [hP, hQ]
  ext s
  constructor
  · -- Assume s ∈ P, we need to show s ∈ Q
    rintro ⟨x, hx⟩
    use (-x)
    nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg ((-x) - 3 / 2)]
  · -- Assume s ∈ Q, we need to show s ∈ P
    rintro ⟨y, hy⟩
    use (-y)
    nlinarith [sq_nonneg (y - 3 / 2), sq_nonneg ((-y) + 3 / 2)]