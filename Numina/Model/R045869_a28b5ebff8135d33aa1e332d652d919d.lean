import Mathlib

theorem algebra_72270 (x y z : ℝ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x^2 + y^2 = -x + 3 * y + z) (h₄ : y^2 + z^2 = x + 3 * y - z)
    (h₅ : x^2 + z^2 = 2 * x + 2 * y - z) :
    (x = 0 ∧ y = 1 ∧ z = -2) ∨ (x = -3 / 2 ∧ y = 5 / 2 ∧ z = -1 / 2) := by
  have h6 : (x - z) * (x + z + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case x - z = 0, so x = z
    exfalso
    have h8 : x = z := by linarith
    have h9 : z = x := by linarith
    contradiction
  · -- Case x + z + 2 = 0, so z = -2 - x
    have hz : z = -2 - x := by linarith
    have h9 : y^2 - z^2 = -3 * x + y + 2 * z := by
      nlinarith
    rw [hz] at h9
    have h10 : (y - x) * (y + x - 1) = 0 := by
      nlinarith [h9]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case y - x = 0, so y = x
      exfalso
      have h13 : y = x := by linarith
      have h14 : x = y := by linarith
      contradiction
    · -- Case y + x - 1 = 0, so y = 1 - x
      have hy : y = 1 - x := by linarith
      rw [hy] at h₃
      rw [hz] at h₃
      have h0 : x * (2 * x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h0) with h14 h15
      · -- Case x = 0
        have hx0 : x = 0 := by linarith
        have hy0 : y = 1 := by linarith
        have hz0 : z = -2 := by linarith
        left
        exact ⟨hx0, hy0, hz0⟩
      · -- Case 2 * x + 3 = 0, so x = -3 / 2
        have hx1 : x = -3 / 2 := by linarith
        have hz1 : z = -1 / 2 := by linarith
        have hy1 : y = 5 / 2 := by linarith
        right
        exact ⟨hx1, hy1, hz1⟩