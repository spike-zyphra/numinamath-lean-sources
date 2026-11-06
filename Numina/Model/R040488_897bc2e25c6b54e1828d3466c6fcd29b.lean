import Mathlib

theorem algebra_267968 {x y z a : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0) (h₅ : a ≠ 0)
    (h₃ : x + y + z = a) (h₄ : 1 / x + 1 / y + 1 / z = 1 / a) :
    x = a ∨ y = a ∨ z = a := by
  have eq1 : y * z * a + x * z * a + x * y * a = x * y * z := by
    have h6 : a ≠ 0 := h₅
    field_simp [h₀, h₁, h₂, h₅] at h₄ ⊢
    nlinarith [sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_pos_of_ne_zero h₂, sq_pos_of_ne_zero h₅, sq_nonneg (x - a), sq_nonneg (y - a), sq_nonneg (z - a)]
  have eq2 : (x - a) * (y - a) * (z - a ) = 0 := by
    have eq3 : x * y * z - a * (y * z + x * z + x * y ) = 0 := by
      nlinarith [eq1]
    have eq4 : (x - a) * (y - a) * (z - a ) = x * y * z - a * (x * y + x * z + y * z ) + a^2 * (x + y + z ) - a^3 := by
      ring
    rw [eq4]
    have eq5 : a^2 * (x + y + z ) = a^3 := by
      have eq8 : x + y + z = a := by linarith [h₃]
      rw [eq8]
      all_goals nlinarith
    have eq7 : x * y * z - a * (x * y + x * z + y * z ) = 0 := by linarith [eq3]
    nlinarith [eq5, eq7]
  cases' (mul_eq_zero.mp eq2) with h8 h9
  cases' (mul_eq_zero.mp h8) with h10 h11
  · left
    linarith
  · right
    left
    linarith
  · right
    right
    linarith