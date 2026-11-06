import Mathlib
open Real

theorem algebra_608406 (x:ℝ) : ((2:ℝ)^(3*x+1) - 17* 2 ^(2*x) + 2^(x+3) = 0) ↔ (x=3 ∨ x = -1) := by
  constructor
  · -- Assume (2:ℝ)^(3*x+1) - 17* 2^(2*x) + 2^(x+3) = 0, prove x=3 ∨ x = -1
    intro h
    have eq1 : (2:ℝ)^(3*x+1) - 17* 2^(2*x) + 2^(x+3) = 0 := h
    have eq2 : (2:ℝ)^(3*x+1) = 2 * ((2:ℝ) ^x)^3 := by
      calc
        (2:ℝ)^(3*x+1) = (2:ℝ)^(3*x) * (2:ℝ) ^ (1:ℝ) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
        _ = ( (2:ℝ)^x )^3 * (2:ℝ) := by
          calc
            (2:ℝ)^(3*x) * (2:ℝ) ^ (1:ℝ) = (2:ℝ)^(3*x) * 2 := by norm_num
            _ = ( (2:ℝ)^x )^3 * 2 := by
              calc
                (2:ℝ)^(3*x) * 2 = (2:ℝ)^(3*x) * (2:ℝ) := by ring
                _ = ( (2:ℝ)^x )^3 * (2:ℝ) := by
                  calc
                    (2:ℝ)^(3*x) * (2:ℝ) = (2:ℝ) ^ (3*x) * (2:ℝ) ^ (1:ℝ) := by ring
                    _ = ( (2:ℝ)^x )^3 * (2:ℝ) ^ (1:ℝ) := by
                      rw [← Real.rpow_natCast, ← Real.rpow_mul]
                      ring_nf
                      all_goals linarith
                    _ = ( (2:ℝ)^x )^3 * (2:ℝ) := by norm_num
        _ = 2 * ((2:ℝ)^x)^3 := by ring
    have eq3 : (2:ℝ)^(2*x) = ((2:ℝ)^x)^2 := by
      calc
        (2:ℝ)^(2*x) = (2:ℝ)^(2*x) := by rfl
        _ = ((2:ℝ)^x)^2 := by
          calc
            (2:ℝ)^(2*x) = (2:ℝ)^(2 * x) := by ring
            _ = ( (2:ℝ)^x )^2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              ring_nf
              all_goals linarith
    have eq4 : (2:ℝ)^(x+3) = 8 * ((2:ℝ)^x) := by
      calc
        (2:ℝ)^(x+3) = (2:ℝ)^x * (2:ℝ)^(3:ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals linarith
        _ = (2:ℝ)^x * (8:ℝ) := by norm_num
        _ = 8 * ((2:ℝ)^x) := by ring
    rw [eq2, eq3, eq4] at eq1
    have h1 : 2 * ((2:ℝ) ^x)^3 - 17 * ((2:ℝ)^x)^2 + 8 * ((2:ℝ) ^x) = 0 := by
      linarith [eq1]
    have h2 : ((2:ℝ) ^x) * (2 * ((2:ℝ)^x)^2 - 17 * ((2:ℝ)^x) + 8) = 0 := by 
      linarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- case h3
      have h4 : (2:ℝ) ^x > 0 := by positivity
      linarith [h3, h4]
    · -- case h4
      have h5 : 2 * ((2:ℝ)^x)^2 - 17 * ((2:ℝ)^x) + 8 = 0 := h4
      have h8 : (2 * ((2:ℝ)^x)^2 - 17 * ((2:ℝ)^x) + 8) = 2 * ((2:ℝ)^x)^2 - 17 * ((2:ℝ)^x) + 8 := by ring
      rw [h8] at h4
      have h5 : ((2:ℝ)^x - 8) * ((2:ℝ)^x - (1/2)) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- case h6
        have h8_eq : (2:ℝ) ^x = (8:ℝ) := by
          linarith
        have hx : x = (3:ℝ) := by
          apply_fun (Real.logb (2:ℝ)) at h8_eq
          have h9 : Real.logb (2:ℝ) ((2:ℝ) ^x) = Real.logb (2:ℝ) (8:ℝ) := by
            rw [h8_eq]
          have h10 : Real.logb (2:ℝ) ((2:ℝ) ^x) = x := by 
            rw [Real.logb_rpow]
            all_goals linarith
          have h11 : Real.logb (2:ℝ) (8:ℝ) = (3:ℝ) := by
            calc
              Real.logb (2:ℝ) (8:ℝ) = Real.logb (2:ℝ) (2 ^ 3) := by norm_num
              _ = (3:ℝ) := by simp [Real.logb_pow]
          linarith [h9, h10, h11]
        left
        linarith
      · -- case h7
        have h9_eq : (2:ℝ) ^x = (1/2:ℝ) := by
          linarith
        have hx : x = (-1:ℝ) := by
          apply_fun (Real.logb (2:ℝ)) at h9_eq
          have h10 : Real.logb (2:ℝ) ((2:ℝ) ^x) = Real.logb (2:ℝ) (1/2:ℝ) := by
            rw [h9_eq]
          have h11 : Real.logb (2:ℝ) ((2:ℝ) ^x) = x := by 
            rw [Real.logb_rpow]
            all_goals linarith
          have h12 : Real.logb (2:ℝ) (1/2:ℝ) = (-1:ℝ) := by
            have h13 : Real.logb (2:ℝ) (1/2:ℝ) = Real.logb (2:ℝ) (1) - Real.logb (2:ℝ) (2:ℝ) := by 
              field_simp [Real.logb_div]
            have h14 : Real.logb (2:ℝ) (1) = (0:ℝ) := by
              simp [Real.logb_one]
            have h15 : Real.logb (2:ℝ) (2:ℝ) = (1:ℝ) := by
              norm_num [Real.logb_eq_iff_rpow_eq]
            rw [h13, h14, h15]
            all_goals linarith
          rw [h11, h12] at h10
          linarith
        right
        linarith
  · -- Assume (x=3 ∨ x = -1)
    rintro (h | h)
    · -- x = 3
      rw [h]
      norm_num
    · -- x = -1
      rw [h]
      norm_num