import Mathlib

open Real

theorem inequalities_1626 (x y : ℝ) :
    x^2 + y^2 / 2 + 4 ≤ x * y + 2 * y ↔ (x = 2 ∧ y = 4) := by
  constructor
  · -- Forward direction: inequality implies x=2 and y=4
    intro h
    have h1 : (x - y / 2) ^ 2 + (1 / 4) * (y - 4) ^ 2 ≤ 0 := by
      nlinarith
    have h2 : (x - y / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y / 2), sq_nonneg (y - 4)]
    have h3 : (1 / 4) * (y - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y / 2), sq_nonneg (y - 4)]
    have hy : y = 4 := by
      nlinarith [sq_nonneg (y - 4)]
    have hx : x = 2 := by
      rw [hy] at h2
      nlinarith [sq_nonneg (x - 2)]
    exact ⟨hx, hy⟩
  · -- Reverse direction: x=2 and y=4 implies inequality
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num