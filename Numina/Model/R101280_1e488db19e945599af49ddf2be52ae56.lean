import Mathlib

theorem algebra_291467 {x y : ℤ} (h₀ : x * y = 4747) (h₁ : x - y = -54) :
    x = 47 ∧ y = 101 ∨ x = -101 ∧ y = -47 := by
  have h2 : x = y - 54 := by linarith
  rw [h2] at h₀
  have h3 : y^2 - 54 * y - 4747 = 0 := by
    nlinarith
  have h4 : (y - 101) * (y + 47) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.1 h4) with hy1 hy2
  · -- Case y - 101 = 0, so y = 101
    have hy : y = 101 := by linarith
    have hx : x = 47 := by
      rw [hy] at h2
      linarith
    left
    exact ⟨hx, hy⟩
  · -- Case y + 47 = 0, so y = -47
    have hy : y = -47 := by linarith
    have hx : x = -101 := by
      rw [hy] at h2
      linarith
    right
    exact ⟨hx, hy⟩