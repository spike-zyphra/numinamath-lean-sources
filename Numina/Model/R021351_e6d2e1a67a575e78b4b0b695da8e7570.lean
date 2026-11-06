import Mathlib

theorem algebra_228754 (x : ℝ) : (5 : ℝ)^(2*x-1) + (5 : ℝ)^(x+1) = 250 ↔ x = 2 := by
  constructor
  · -- Assume (5 : ℝ)^(2*x-1) + (5 : ℝ)^(x+1) = 250, prove x = 2
    intro h
    have h1 : (5 : ℝ) ^ (2 * x - 1) = ( (5 : ℝ) ^ x ) ^ 2 / (5 : ℝ) := by
      have h22 : (5 : ℝ) ^ (2 * x - 1) = ( (5 : ℝ) ^ (2 * x) ) / ( (5 : ℝ) ^ (1 : ℝ) ) := by
        rw [show (2 * x - 1 : ℝ) = (2 * x : ℝ) - (1 : ℝ) by ring]
        rw [Real.rpow_sub]
        all_goals
          linarith
      have h33 : ( (5 : ℝ) ^ (2 * x) ) = ( (5 : ℝ) ^ x ) ^ 2 := by
        calc
          ( (5 : ℝ) ^ (2 * x) ) = ( 5 : ℝ ) ^ (2 * x : ℝ) := by norm_num
          _ = ( ( (5 : ℝ) ^ x ) ^ 2 : ℝ ) := by
            rw [show (2 * x : ℝ) = (x : ℝ) * 2 by ring]
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring_nf
            all_goals linarith
      have h44 : ( (5 : ℝ) ^ (1 : ℝ) ) = (5 : ℝ) := by
        simp
      rw [h22, h33, h44]
    have h2 : (5 : ℝ) ^ (x + 1) = (5 : ℝ) ^ x * (5 : ℝ) := by
      rw [show (x + 1 : ℝ) = x + 1 by ring]
      rw [Real.rpow_add]
      ring_nf
      all_goals linarith
    rw [h1, h2] at h
    have ht : ( (5 : ℝ ) ^ x ) ^ 2 + (5 : ℝ ) ^ x * (25 : ℝ ) = 1250 := by 
      have eq1 : ( (5 : ℝ ) ^x ) ^ 2 / (5 : ℝ ) + ( (5 : ℝ ) ^x * (5 : ℝ ) ) = 250 := by
        linarith
      have eq2 : ( (5 : ℝ ) ^x ) ^ 2 / (5 : ℝ ) + ( (5 : ℝ ) ^x * (5 : ℝ ) ) = ( (5 : ℝ ) ^x ) ^ 2 /5 + (5 : ℝ ) ^x * 5 := by 
        ring_nf 
      have hht4 : ( (5 : ℝ ) ^x )^ 2 + (5 : ℝ )^ x * 25 = 1250 := by
        have eq3 : ( (5 : ℝ ) ^x ) ^ 2 /5 + (5 : ℝ ) ^x * 5 = 250 := by
          linarith [eq1, eq2]
        have eq4 : ( (5 : ℝ ) ^x )^ 2 + (5 : ℝ )^ x * 25 = 1250 := by
          field_simp [(show (5 : ℝ) ≠ 0 by norm_num )] at eq3 ⊢
          nlinarith
        linarith
      nlinarith
    have h5 : (5 : ℝ ) ^ x = 25 := by 
      have h6 : (5 : ℝ ) ^ x > 0 := by positivity
      have h11 : ( (5 : ℝ ) ^ x ) ^ 2 + ( 25 : ℝ ) * ( (5 : ℝ ) ^ x ) - ( 1250 : ℝ ) = 0 := by 
        linarith 
      nlinarith [ sq_nonneg ( (5 : ℝ ) ^ x - 25 ), sq_nonneg ( (5 : ℝ ) ^ x + 50 ), h6 ]
    have h50 : x = 2 := by
      have h6 : (5 : ℝ ) ^ (x) = 25 := by
        linarith [ h5 ]
      have h7 : x = (2 : ℝ ) := by
        have h8 : (5 : ℝ ) ^ (x) = (25 : ℝ ) := by
          linarith
        have h9 : (25 : ℝ ) = (5 : ℝ ) ^ (2 : ℝ ) := by
          norm_num
        rw [ h9 ] at h8
        have h11 : x = (2 : ℝ ) := by
          have h12 : x = (2 : ℝ ) := by 
            apply_fun (Real.logb (5 : ℝ ) ) at h8
            have h121 : Real.logb (5 : ℝ ) ( 5 ^ x ) = x := by 
                rw [ Real.logb_rpow ]
                all_goals norm_num
            have h13 : Real.logb (5 : ℝ ) ( (5 : ℝ ) ^ (2 : ℝ ) ) = (2 : ℝ ) := by 
                rw [ Real.logb_rpow ]
                all_goals norm_num
            linarith [ h8, h121, h13 ]
          linarith
        linarith
      linarith
    linarith
  · -- Assume x = 2, prove the equation
    intro h
    rw [ h ]
    norm_num