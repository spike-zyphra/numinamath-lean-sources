import Mathlib

open Real


theorem number_theory_641399 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (R : ℕ → ℕ) 
  (hR : ∀ k, R k = ∑ i ∈ Finset.range k, 10 ^ i) :
  (Nat.digits 10 (R a * R b)).length = a + b - 1 := by 
  have h1 : ∀ k, ∑ i ∈ Finset.range k, (10 : ℝ) ^ i = 
    ((10 : ℝ) ^ k - 1) / 9 := by 
    intro k
    have gt1 : (10 : ℝ) > 1 := by linarith
    have neq : (10 : ℝ) ≠ 1 := by 
      linarith
    rw [geom_sum_eq neq k]
    norm_num
  have Rabneq : R a * R b ≠ 0 := by 
    have Rapos : R a > 0 := by 
      rw [hR]
      apply Finset.sum_pos
      intro x hx
      positivity
      refine Finset.Aesop.range_nonempty ?_
      linarith
    have Rbpos : R b > 0 := by
      rw [hR]
      apply Finset.sum_pos
      intro x hx
      positivity
      refine Finset.Aesop.range_nonempty ?_
      linarith
    have pos : R a * R b > 0 := by 
      positivity
    linarith
  rw [Nat.digits_len]
  have h2 : Nat.log 10 (R a * R b) = a + b - 2 := by 
    refine (Nat.log_eq_iff ?_).mpr ?_
    · right
      exact ⟨by linarith, Rabneq⟩
    · constructor
      · -- first prove the inequality in the type ℝ, then use cast to get ℕ
        have aux1 : (10 : ℝ) ^ (a + b - 2) ≤ R a * R b := by 
          rw [hR, hR]
          norm_num
          rw [h1, h1]
          field_simp
          refine (le_div_iff₀ ?_).mpr ?_ 
          · positivity
          · 
            have aux2 : (10 : ℝ) ^ (a + b - 2) = 10 ^ (a + b - 2 : ℝ) := by 
              have cast1 : (a + b - 2 : ℕ) = ((a : ℝ) + b - 2) := by 
                have cast2 : (a + b - 2 : ℕ) = ((a : ℤ) + b - 2) := by 
                  have ge1 : (a : ℝ) + b - 2 ≥ 0 := by 
                    have age1 : (a : ℝ) ≥ 1 := by 
                      norm_cast
                    have bge1 : (b : ℝ) ≥ 1 := by 
                      norm_cast
                    linarith
                  omega
                have cast3 : ((a : ℤ) + b - 2) = ((a : ℝ) + b - 2) := by  
                  norm_num
                calc  
                  _ = ↑((a + b - 2 : ℕ) : ℤ) := by 
                    simp
                  _ = _ := by 
                    rw [cast2, ← cast3]
                    simp 
              rw [←cast1]
              norm_cast
            rw [aux2]
            have cast2 : (10 : ℝ) ^ a = 10 ^ (a : ℝ) := by
              norm_cast
            have cast3 : (10 : ℝ) ^ b = 10 ^ (b : ℝ) := by
              norm_cast 
            rw [cast2, cast3, Real.rpow_sub]
            ring_nf
            have aux3 : 1 - (10 : ℝ) ^ (a : ℝ) + ((10 : ℝ) ^ (a : ℝ) * 10 ^ (b : ℝ) - 10 ^ (b : ℝ)) = ((10 : ℝ) ^ (a + b : ℝ)) * ((1 - (10 : ℝ) ^ (-a : ℝ)) * (1 - (10 : ℝ) ^ (-b : ℝ))):= by 
              ring_nf
              rw [←rpow_add, ←rpow_add, ←rpow_add, ←rpow_add]
              ring_nf 
              linarith
              linarith
              linarith
              linarith
            rw [aux3]
            apply mul_le_mul
            simp
            have ge1 : (1 - (10 : ℝ) ^ (-a : ℝ)) ≥ 9 / 10 := by 
              calc 
                _ ≥ (1 - (10 : ℝ) ^ (- 1 : ℝ)) := by 
                  have aux4 : (10 : ℝ) ^ (-a : ℝ) ≤ (10 : ℝ) ^ (- 1 : ℝ) := by 
                    simp 
                    exact ha
                  linarith
                _ = 9 / 10 := by
                  norm_num
            have ge2 : (1 - (10 : ℝ) ^ (-b : ℝ)) ≥ 9 / 10 := by
              calc
                _ ≥ (1 - (10 : ℝ) ^ (- 1 : ℝ)) := by
                  have aux5 : (10 : ℝ) ^ (-b : ℝ) ≤ (10 : ℝ) ^ (- 1 : ℝ) := by
                    simp
                    exact hb
                  linarith
                _ = 9 / 10 := by
                  norm_num
            have pos1 : 1 ≥ (10 : ℝ) ^ (-a : ℝ) := by 
              refine rpow_le_one_of_one_le_of_nonpos ?_ ?_
              linarith
              linarith
            obtain ge3 := mul_le_mul ge1 ge2 (by norm_num) (by linarith)
            linarith
            linarith
            positivity
            positivity
        norm_cast at aux1
      · -- first prove the inequality in the type ℝ, then use cast to get ℕ
        have aux1 : R a * R b < (10 : ℝ) ^ (a + b - 2 + 1) := by 
          rw [hR, hR]
          norm_num
          rw [h1, h1]
          field_simp
          have eq1 : a + b - 2 + 1 = a + b - 1 := by 
            omega
          rw [eq1]
          calc 
            _ < (10 : ℝ) ^ a * 10 ^ b / (9 * 9) := by 
              have lt_aux : (10 ^ a - 1) * (10 ^ b - 1) < (10 : ℝ) ^ a * 10 ^ b := by 
                apply mul_lt_mul
                linarith
                linarith
                have aux2 : 1 < (10 : ℝ) ^ b := by 
                  refine one_lt_pow₀ ?_ ?_
                  linarith
                  linarith
                linarith
                positivity
              refine (div_lt_div_iff_of_pos_right ?_).mpr lt_aux
              positivity
            _ ≤ _ := by 
              have cast1 : (10 : ℝ) ^ ((a + b - 1 : ℕ)) = 
                (10 : ℝ) ^ (a + b - (1 : ℝ)) := by 
                have cast2 : (a + b - (1 : ℝ)) = (a + b - 1 : ℕ) := by 
                  calc 
                    _ = ↑((a : ℤ) + b - 1) := by 
                      norm_num
                    _ = ↑((a + b - 1 : ℕ) : ℤ) := by 
                      have aux1 : (a + b - 1 : ℕ) = ((a : ℤ) + b - 1) := by 
                        omega
                      rw [aux1]
                    _ = _ := by 
                      simp
                rw [cast2]
                norm_cast
              have cast2 : (10 : ℝ) ^ a * (10 : ℝ) ^ b =  (10 : ℝ) ^ (a : ℝ) * (10 : ℝ) ^ (b : ℝ) := by 
                norm_cast
              rw [cast1, rpow_sub, cast2, ←rpow_add]
              refine div_le_div_of_nonneg_left ?_ ?_ ?_
              positivity
              norm_num
              norm_num
              norm_num
              norm_num
        norm_cast at aux1
  rw [h2]
  omega
  linarith
  exact Rabneq