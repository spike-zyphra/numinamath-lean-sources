import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_117364 {p q : ℝ}
  (hp : ∀ x ∈ Ico (-4) (-3), p = x ^ 2 - (1 / (1 + sqrt 2) + ∑ i ∈ Finset.range 24, 1 / (sqrt (i + 1) + sqrt (i + 2))) * x + q)
  (hq : q ∈ Ico (-4) (-3) ∩ {x | abs (2 * x - 1) < 3}) :
  p = -1 / 2 := by
  rcases hq with ⟨⟨hq1, hq2⟩, hq3⟩
  have hq4 : -1 < q := by
    have h1 : abs (2 * q - 1) < 3 := hq3
    rw [abs_lt] at h1
    linarith
  have hq5 : q < 2 := by
    have h1 : abs (2 * q - 1) < 3 := hq3
    rw [abs_lt] at h1
    linarith
  linarith