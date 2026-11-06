import Mathlib

theorem algebra_234647 {x y z : ℝ} (h1 : x * y + 5 * y * z - 6 * x * z = -2 * z)
    (h2 : 2 * x * y + 9 * y * z - 9 * x * z = -12 * z) (h3 : y * z - 2 * x * z = 6 * z) :
    (x = -2 ∧ y = 2 ∧ z = 1 / 6) ∨ (x = x ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = y ∧ z = 0) := by
  by_cases h : z = 0
  · -- Case where z = 0. Then h1 and h2 imply x * y = 0
    have h1' : x * y = 0 := by
      rw [h] at h1
      linarith
    cases' (mul_eq_zero.mp h1') with h4 h5
    · -- Case x = 0
      right
      right
      constructor
      · linarith
      constructor
      · linarith
      · linarith
    · -- Case y = 0
      right
      left
      constructor
      · linarith
      constructor
      · linarith
      · linarith
  · -- Case where z ≠ 0
    have h4 : y = 2 * x + 6 := by
      apply (mul_left_inj' h).mp
      linarith [h3]
    rw [h4] at h1 h2
    have h5 : z * (x + 2) = 0 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (z)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case z = 0, which is a contradiction
      exfalso
      apply h
      linarith
    · -- Case x + 2 = 0, so x = -2
      have hx1 : x = -2 := by linarith
      have hy1 : y = 2 := by
        rw [hx1] at h4
        linarith
      have hz1 : z = 1 / 6 := by
        rw [hx1] at h1
        linarith
      left
      constructor
      · linarith
      constructor
      · linarith
      · linarith