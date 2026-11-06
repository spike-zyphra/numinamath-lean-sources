import Mathlib

open Real


theorem algebra_203408 {F G : ℝ → ℝ}
    (hF : F = fun x => log ((1 + x) / (1 - x)))
    (hG : ∀ x, G x = F ((3 * x + x ^ 3) / (1 + 3 * x ^ 2))) :
    G = fun x => 3 * F x := by 
  funext x 
  have hGx : G x = F ((3 * x + x^3) / (1 + 3 * x^2)) := hG x 
  have h1 : G x = 3 * F x := by 
    rw [hGx]
    rw [hF]
    simp
    have h1' : log (( (1 + ( (3 * x + x^3) / (1 + 3 * x^2) ) ) ) / (1 - ( (3 * x + x^3) / (1 + 3 * x^2) )) ) = 3 * log ((1 + x) / (1 - x)) := by 
      by_cases h1_sub : 1 - x = 0 
      · -- Case 1 - x = 0, so x = 1 
        have hx1 : x = 1 := by linarith 
        rw [hx1] 
        norm_num [log_zero] 
      · -- Case 1 - x ≠ 0 
        have hx1 : 1 - x ≠ 0 := h1_sub 
        have eq1 : (1 + ( (3 * x + x^3) / (1 + 3 * x^2) )) = ( (1 + x)^3 / (1 + 3 * x^2) ) := by 
          field_simp [(show 1 + 3 * x^2 ≠ 0 by nlinarith [sq_nonneg x] )] 
          ring 
        have eq2 : (1 - ( (3 * x + x^3) / (1 + 3 * x^2) )) = ( (1 - x)^3 / (1 + 3 * x^2) ) := by 
          field_simp [(show 1 + 3 * x^2 ≠ 0 by nlinarith [sq_nonneg x] )] 
          ring 
        have eq3 : ( (1 + ( (3 * x + x^3) / (1 + 3 * x^2) ) ) / ( (1 - ( (3 * x + x^3) / (1 + 3 * x^2) ) ) ) ) = ( ( (1 + x) / (1 - x) )^3 ) := by 
          have eq31 : ( (1 + ( (3 * x + x^3) / (1 + 3 * x^2) ) ) / ( (1 - ( (3 * x + x^3) / (1 + 3 * x^2) ) ) ) ) = ( ( (1 + x) / (1 - x) )^3 ) := by 
            have h5 : (1 + ( (3 * x + x^3) / (1 + 3 * x^2) ) ) = ( (1 + x)^3 / (1 + 3 * x^2) ) := eq1 
            have h6 : (1 - ( (3 * x + x^3) / (1 + 3 * x^2) ) ) = ( (1 - x)^3 / (1 + 3 * x^2) ) := eq2 
            rw [h5, h6] 
            have h_pos1 : (1 + 3 * x ^ 2) ≠ 0 := by 
              nlinarith [sq_nonneg x]
            by_cases h2 : 1 - x = 0 
            · -- This is impossible; we are in case 1 - x ≠ 0 
              exfalso 
              apply h1_sub 
              linarith 
            · -- Case 1 - x ≠ 0, so we have expressions 
              have hx7 : 1 - x ≠ 0 := by 
                intro h_eq 
                apply h1_sub 
                linarith 
              field_simp [h_pos1, hx7] 
              <;> ring_nf 
          linarith [eq31] 
        have h3 : log ( ( (1 + ( (3 * x + x^3) / (1 + 3 * x^2) ) ) ) / ( 1 - ( (3 * x + x^3) / (1 + 3 * x^2) ) ) ) = 3 * log ( ( (1 + x) / (1 - x) ) ) := by 
          rw [eq3] 
          have h4 : log ( ( ( (1 + x) / (1 - x) )^3 ) ) = 3 * log ( ( (1 + x) / (1 - x) ) ) := by 
            simp [log_pow] 
          linarith [h4] 
        linarith 
    linarith [h1'] 
  exact h1