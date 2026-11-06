import Mathlib

theorem algebra_188108 {x y z : ℝ} (h₀ : x + y + z = 6) (h₁ : x * y + y * z + z * x = 11)
    (h₂ : x * y * z = 6) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = 1 ∧ y = 3 ∧ z = 2) ∨ (x = 2 ∧ y = 1 ∧ z = 3) ∨
    (x = 2 ∧ y = 3 ∧ z = 1) ∨ (x = 3 ∧ y = 1 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 1) := by
  have h3 : z = 6 - x - y := by linarith
  rw [h3] at h₁ h₂
  have h4 : x ^ 2 + y ^ 2 + x * y - 6 * (x + y) + 11 = 0 := by
    nlinarith
  have h6 : (x - 1) * (x - 2) * (x - 3) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (6 - x - y)), sq_nonneg (y - (6 - x - y))]
  cases' (mul_eq_zero.mp h6) with h7 h7
  cases' (mul_eq_zero.mp h7) with h7 h7
  · -- Case x - 1 = 0, so x = 1
    have hx1 : x = 1 := by linarith
    have h8 : y ^ 2 - 5 * y + 6 = 0 := by
      nlinarith [hx1]
    have h9 : (y - 2) * (y - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with hy2 hy3
    · -- Case y - 2 = 0, so y = 2
      have hy2' : y = 2 := by linarith
      have hz3 : z = 3 := by
        nlinarith [hx1, hy2']
      simp [hx1, hy2', hz3]
    · -- Case y - 3 = 0, so y = 3
      have hy3' : y = 3 := by linarith
      have hz2 : z = 2 := by
        nlinarith [hx1, hy3']
      simp [hx1, hy3', hz2]
  · -- Case x - 2 = 0, so x = 2
    have hx2 : x = 2 := by linarith
    have h8 : y ^ 2 - 4 * y + 3 = 0 := by
      nlinarith [hx2]
    have h9 : (y - 1) * (y - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with hy1 hy3
    · -- Case y - 1 = 0, so y = 1
      have hy1' : y = 1 := by linarith
      have hz3 : z = 3 := by
        nlinarith [hx2, hy1']
      simp [hx2, hy1', hz3]
    · -- Case y - 3 = 0, so y = 3
      have hy3' : y = 3 := by linarith
      have hz1 : z = 1 := by
        nlinarith [hx2, hy3']
      simp [hx2, hy3', hz1]
  · -- Case x - 3 = 0, so x = 3
    have hx3 : x = 3 := by linarith
    have h8 : y ^ 2 - 3 * y + 2 = 0 := by
      nlinarith [hx3]
    have h9 : (y - 1) * (y - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with hy1 hy2
    · -- Case y - 1 = 0, so y = 1
      have hy1' : y = 1 := by linarith
      have hz2 : z = 2 := by
        nlinarith [hx3, hy1']
      simp [hx3, hy1', hz2]
    · -- Case y - 2 = 0, so y = 2
      have hy2' : y = 2 := by linarith
      have hz1 : z = 1 := by
        nlinarith [hx3, hy2']
      simp [hx3, hy2', hz1]