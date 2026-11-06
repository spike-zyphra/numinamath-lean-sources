import Mathlib

theorem algebra_188060 (x y : ℝ) :
    x^2 + x * y + y = 1 ∧ y^2 + x * y + x = 1 ↔ (x = -1 ∧ y = -1) ∨ (x = x ∧ y = 1 - x) := by
  constructor
  · -- Assume both equations are true
    rintro ⟨h1, h2⟩
    have h3 : (x - y) * (x + y - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case x - y = 0, so x = y
      have h6 : x = y := by linarith
      have h7 : 2 * x^2 + x - 1 = 0 := by
        rw [show y = x by linarith [h6]] at h1
        nlinarith
      have h8 : (x - (1/2)) * (x + 1) = 0 := by nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case x = 1/2, so y = 1/2
        have hx : x = (1 / 2 : ℝ) := by linarith
        have hy : y = (1 / 2 : ℝ) := by linarith [h6, hx]
        right
        constructor
        · -- x = x
          rfl
        · -- y = 1 - x
          linarith [hy, hx]
      · -- Case x = -1, so y = -1
        have hx : x = (-1 : ℝ) := by linarith
        have hy : y = (-1 : ℝ) := by linarith [h6, hx]
        left
        constructor
        · -- x = -1
          linarith
        · -- y = -1
          linarith
    · -- Case x + y - 1 = 0, so y = 1 - x
      have h8 : y = 1 - x := by linarith
      right
      constructor
      · -- x = x
        rfl
      · -- y = 1 - x
        linarith
  · -- Assume the bi-implication
    rintro (h | h)
    · -- Case (x = -1 ∧ y = -1)
      rcases h with ⟨hx, hy⟩
      constructor
      · -- First equation
        rw [hx, hy]
        norm_num
      · -- Second equation
        rw [hx, hy]
        norm_num
    · -- Case (x = x ∧ y = 1 - x)
      rcases h with ⟨hx, hy⟩
      constructor
      · -- First equation
        rw [show y = 1 - x by linarith [hy]]
        nlinarith
      · -- Second equation
        rw [show y = 1 - x by linarith [hy]]
        nlinarith