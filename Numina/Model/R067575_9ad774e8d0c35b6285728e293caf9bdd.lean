import Mathlib

theorem algebra_187193 {u v w : ℝ} (h1 : v - u = 1) (h2 : w - v = 1)
    (h3 : (u - 1)^3 + (v - 2)^3 + (w - 3)^3 = 3) :
    u = 2 ∧ v = 3 ∧ w = 4 := by
  have h4 : v = u + 1 := by linarith
  have h5 : w = u + 2 := by
    rw [h4] at h2
    linarith
  rw [h4, h5] at h3
  have h6 : (u - 1 : ℝ) ^ 3 = 1 := by
    ring_nf at h3 ⊢
    nlinarith [sq_nonneg (u - 1), sq_nonneg ((u - 1 : ℝ) ^ 2), sq_nonneg ((u - 1 + 1) : ℝ)]
  have h7 : u - 1 = 1 := by
    have h8 : (u - 1 : ℝ) ^ 3 - 1 = 0 := by linarith
    have h9 : (u - 1 - 1) * ((u - 1) ^ 2 + (u - 1) + 1) = 0 := by
      ring_nf at h8 ⊢
      <;> nlinarith
      <;> ring_nf at h8 ⊢ <;> nlinarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- Real solution u - 1 -1 =0 which implies u =2
      nlinarith
    · -- Show that the quadratic has no real solution
      have h12 : (u - 1) ^ 2 + (u - 1) + 1 > 0 := by
        nlinarith [sq_nonneg ((u - 1) + 1 / 2)]
      have h13 : (u - 1) ^ 2 + (u - 1) + 1 = 0 := by linarith
      nlinarith
  have h8 : u = 2 := by linarith
  have h9 : v = 3 := by
    rw [h8] at h4
    linarith
  have h10 : w = 4 := by
    rw [h8] at h5
    linarith
  exact ⟨h8, h9, h10⟩