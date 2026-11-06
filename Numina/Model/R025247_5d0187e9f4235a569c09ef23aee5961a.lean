import Mathlib

theorem algebra_230850 {x y z : ℝ} (h1 : x + y - z = -1) (h2 : x^2 - y^2 + z^2 = 1) (h3 : -x^3 + y^3 + z^3 = -1) :
    (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = -1 ∧ z = -1) := by
  have h4 : z = x + y + 1 := by linarith
  rw [h4] at h2 h3
  have h5 : x^2 + x * (y + 1) + y = 0 := by
    nlinarith
  -- From h5 it can be factored into (x + 1)(x + y) = 0
  have h6 : (x + 1) * (x + y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case h7 : x + 1 = 0, so x = -1.
    have hx1 : x = -1 := by linarith
    have hy1 : y = -1 := by
      -- From h1 : x + y - z = -1. We expressed z = x + y + 1. Now x = -1.
      -- So z = -1 + y + 1 = y
      -- From h2 (transformed) which is x^2 + x * (y+1) + y =0 (h5).
      -- Substituting x=-1, we get 0 = 0. Does not help.
      -- Substitute x=-1 into h3.
      -- h3 := -x ^ 3 + y ^ 3 + (x + y + 1) ^ 3 = -1.
      have h_eq_y : -(-1:ℝ) ^ 3 + y ^ 3 + (y) ^ 3 = -1 := by
        rw [hx1] at h3
        ring_nf at h3 ⊢
        linarith
      have hx_eq : y = -1 := by
        have eq1 : -(-1:ℝ) ^ 3 + y ^ 3 + y ^ 3 = -1 := h_eq_y
        have eq2 : 2 * y^3 = -2 := by nlinarith
        have eq3 : y^3 = -1 := by nlinarith
        have eq4 : y = -1 := by
          have h3 : y^3 + 1 = 0 := by linarith
          have h4 : y^3 + 1 = (y + 1) * (y^2 - y + 1) := by ring
          rw [h4] at h3
          cases' (mul_eq_zero.1 h3) with h14 h15
          · linarith
          · 
            -- From h6 : y^2 - y + 1 = 0. This is impossible, since discriminant.
            have h7 : y^2 - y + 1 > 0 := by 
                nlinarith [sq_nonneg (y - 1 / 2)]
            -- only intersection is from quadratic not having solution.
            nlinarith [h7, sq_nonneg (y + 1 / 2)]
        linarith
      linarith
    have hz1 : z = -1 := by
      rw [hx1, hy1] at h4
      linarith
    right
    tauto
  · -- Case h8 : x + y = 0, so y = -x.
    have h11 : y = -x := by linarith
    have hz1 : z = 1 := by
      rw [show y = -x by linarith] at h4
      linarith
    have hx1 : x = 1 := by
      have eq1 : -x ^ 3 + (-x) ^ 3 + (1:ℝ) ^ 3 = -1 := by 
        nlinarith [sq_nonneg (x ^ 2 + 1), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x + 1)]
      have eq2 : x^3 = 1 := by 
        nlinarith [sq_nonneg (x ^ 2 + 1), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x + 1)]
      have eq4 : x = 1 := by 
        have h7 : x^3 - 1 = 0 := by linarith
        have h72 : x^3 - 1 = (x - 1) * (x^2 + x + 1) := by ring
        rw [h72] at h7
        cases' (mul_eq_zero.1 h7) with h14 h15
        · -- x - 1 = 0 
          linarith
        · 
          have h6 : x^2 + x + 1 > 0 := by 
            nlinarith [sq_nonneg (x + 1 / 2)]
          have h8 : x^2 + x + 1 = 0 := by linarith
          nlinarith [h6, h8]
      linarith
    have hy1 : y = -1 := by 
      rw [hx1] at h11
      linarith
    left
    constructor
    · linarith
    constructor
    · linarith
    · linarith