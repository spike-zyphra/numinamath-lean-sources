import Mathlib

theorem algebra_154520 (f : ℝ → ℝ) (hf : f = fun x => 2^(3*x+1) - 17 * 2^(2*x) + 2^(x+3)) :
    ∏ᶠ x ∈ {x | f x = 0}, x = -3 := by
  have h1 : {x | f x = 0} = {-1, 3} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0, prove x ∈ {-1, 3}
      intro hx
      have h_eq : (2 : ℝ) ^ (3 * x + 1) - 17 * (2 : ℝ) ^ (2 * x) + (2 : ℝ) ^ (x + 3) = 0 := by
        simpa using hx

      have h_eq2 : (2 : ℝ) ^ (3 * x + 1) = 2 * ((2 : ℝ) ^ x) ^ 3 := by 
        have h_pow1 : ((2 : ℝ) ^ (3 * x + 1) ) = ((2 : ℝ) ^ (3 * x) ) * ((2 : ℝ) ^ (1 : ℝ)) := by 
          rw [← Real.rpow_add]
          ring_nf 
          all_goals linarith 
        have h_pow2 : ((2 : ℝ) ^ (3 * x) ) = ((2 : ℝ) ^ x ) ^ 3 := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf 
          all_goals linarith 
        rw [h_pow1] 
        rw [h_pow2] 
        norm_num 
        <;> ring_nf 

      have h_eq3 : (2 : ℝ) ^ (x + 3) = 8 * ((2 : ℝ) ^ x) := by 
        calc 
          (2 : ℝ) ^ (x + 3) = (2 : ℝ) ^ x * (2 : ℝ) ^ (3 : ℝ) := by 
            rw [← Real.rpow_add]
            ring_nf 
            all_goals linarith 
          _ = (2 : ℝ) ^ x * 8 := by norm_num 
          _ = 8 * ((2 : ℝ) ^ x) := by ring_nf

      have h_eq4 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by 
        calc 
          (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x ) ^ 2 := by 
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring_nf 
            all_goals linarith 
          _ = ((2 : ℝ) ^ x ) ^ 2 := by 
            norm_num

      rw [h_eq2, h_eq3, h_eq4] at h_eq

      have h_eq5 : ((2 : ℝ) ^ x) * (2 * ((2 : ℝ) ^ x) ^ 2 - 17 * ((2 : ℝ) ^ x) + 8) = 0 := by 
        linarith

      cases' (mul_eq_zero.1 h_eq5) with h2_eq0 h2_ne0 
      · -- Show that ((2 : ℝ) ^ x) ≠ 0 
        have h2_pos : (2 : ℝ) ^ x > 0 := by positivity 
        linarith -- contradiction 
      · -- Solve the quadratic factor 
        have h2 : 2 * ((2 : ℝ) ^ x) ^ 2 - 17 * ((2 : ℝ) ^ x) + 8 = 0 := by 
          linarith 
        have h4 : ((2 : ℝ) ^ x - 8) * ((2 : ℝ) ^ x - (1 / 2)) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h4) with h5 h6 
        · -- Solve 2^x = 8 
          have h7 : (2 : ℝ) ^ x = (8 : ℝ) := by linarith 
          have h8 : x = (3 : ℝ) := by 
            apply_fun (Real.logb (2 : ℝ) ) at h7 
            have h9 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x ) = Real.logb (2 : ℝ) (8 : ℝ) := by 
              linarith [h7] 
            have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x ) = x := by 
              rw [Real.logb_rpow]
              all_goals linarith 
            have h11 : Real.logb (2 : ℝ) (8 : ℝ) = 3 := by 
              rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
            rw [h10] at h9 
            rw [h11] at h9 
            linarith 
          right 
          linarith 
        · -- Solve 2^x = 1/2 
          have h7 : (2 : ℝ) ^ x = (1 / 2 : ℝ) := by linarith 
          have h8 : x = (-1 : ℝ) := by 
            apply_fun (Real.logb (2 : ℝ) ) at h7 
            have h9 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x ) = Real.logb (2 : ℝ) (1 / 2 : ℝ) := by 
              linarith [h7] 
            have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x ) = x := by 
              rw [Real.logb_rpow]
              all_goals linarith 
            have h11 : Real.logb (2 : ℝ) (1 / 2 : ℝ) = -1 := by 
              rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
            rw [h10] at h9 
            rw [h11] at h9 
            linarith 
          left 
          linarith 
    · -- Assume x ∈ {-1, 3}, prove f x = 0
      rintro (h_eq | h_eq )
      · -- x = -1 
        rw [show x = (-1 : ℝ) by linarith [h_eq] ] 
        norm_num [Real.rpow_mul ]
      · -- x = 3 
        rw [show x = (3 : ℝ) by linarith [h_eq] ]
        norm_num [Real.rpow_mul ]
  rw [h1]
  rw [finprod_mem_pair (by norm_num ) ]
  all_goals norm_num