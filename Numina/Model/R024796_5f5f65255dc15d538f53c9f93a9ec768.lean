import Mathlib

theorem algebra_326675 {x y z t : ℝ} (h₀ : x * y + y * z + z * x = 1)
    (h₁ : y * z + z * t + t * y = 1) (h₂ : z * t + t * x + x * z = 1)
    (h₃ : t * x + x * y + y * t = 1) :
    x = y ∧ y = z ∧ z = t ∧ t = Real.sqrt 3 / 3 ∨ x = y ∧ y = z ∧ z = t ∧ t = -Real.sqrt 3 / 3 := by

  have eq1 : (x - t) * (y + z) = 0 := by 
    nlinarith
  have eq2 : (y - x) * (z + t) = 0 := by
    nlinarith
  have eq3 : (z - y) * (t + x) = 0 := by
    nlinarith
  have eq4 : (t - z) * (x + y) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq1) with h4 h5
  · -- case1 x - t = 0, so x = t
    have ht : t = x := by linarith
    have eq2' : (y - x) * (z + t) = 0 := by 
      nlinarith
    rw [ht] at eq2'
    cases' (mul_eq_zero.mp eq2') with h6 h7
    · -- h6 : y - x = 0 
      have hy : y = x := by linarith
      have eq3' : (z - y) * (t + x) = 0 := by 
        nlinarith 
      rw [hy, ht] at eq3'
      cases' (mul_eq_zero.mp eq3') with h8 h9
      · -- h8 : z - x = 0 
        have hz : z = x := by linarith 
        have h7 : 3 * x ^ 2 = 1 := by
          rw [show y = x by linarith [hy], show z = x by linarith [hz]] at h₀
          nlinarith 
        have h9 : x = Real.sqrt 3 / 3 ∨ x = -Real.sqrt 3 / 3 := by 
          have h10 : x ^ 2 - (1 / 3) = 0 := by
            nlinarith 
          have h11 : (x - Real.sqrt 3 / 3) * (x + Real.sqrt 3 / 3) = 0 := by
            nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
          cases' (mul_eq_zero.mp h11) with h12 h13 
          · -- h12 : x - Real.sqrt 3 / 3 = 0 
            left 
            linarith 
          · -- h13 : x + Real.sqrt 3 / 3 = 0 
            right 
            linarith 
        cases' h9 with h10 h11 
        · -- x = Real.sqrt 3 / 3 
          have h0 : x = Real.sqrt 3 / 3 := h10 
          have h12 : y = Real.sqrt 3 / 3 := by linarith [h0, hy] 
          have h13 : z = Real.sqrt 3 / 3 := by linarith [h0, hz] 
          have h14 : t = Real.sqrt 3 / 3 := by linarith [h0, ht] 
          left 
          constructor 
          · -- x = y 
            linarith 
          constructor 
          · -- y = z 
            linarith 
          constructor 
          · -- z = t 
            linarith 
          · -- t = Real.sqrt 3 / 3 
            linarith 
        · -- x = -Real.sqrt 3 / 3 
          have h0 : x = -Real.sqrt 3 / 3 := h11 
          have h12 : y = -Real.sqrt 3 / 3 := by linarith [h0, hy] 
          have h13 : z = -Real.sqrt 3 / 3 := by linarith [h0, hz] 
          have h14 : t = -Real.sqrt 3 / 3 := by linarith [h0, ht] 
          right 
          constructor 
          · -- x = y 
            linarith 
          constructor 
          · -- y = z 
            linarith 
          constructor 
          · -- z = t 
            linarith 
          · -- t = -Real.sqrt 3 / 3 
            linarith 
      · -- h9 : t + x = 0 
        have h10 : x = 0 := by 
          nlinarith 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- h7 : z + x = 0 
      have h11 : z = -x := by linarith 
      have h12 : -x ^ 2 = 1 := by 
        rw [show z = -x by linarith, show t = x by linarith] at h₂ 
        nlinarith 
      nlinarith [sq_nonneg x]
  · -- case2 y + z = 0
    have h10 : z = -y := by linarith 
    rw [show z = -y by linarith] at h₀ 
    nlinarith [sq_nonneg y]