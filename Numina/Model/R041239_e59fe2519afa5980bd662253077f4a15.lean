import Mathlib

theorem number_theory_96003 :
    Set.ncard {n : ℕ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧ ∃ k : ℕ, r = k / 999} = 660 := by 
  have h1 : {n : ℕ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧ ∃ k : ℕ, r = k / 999} = Finset.image (fun (k : ℕ) => ( (k : ℚ) / 999).num.natAbs ) (Finset.Icc 1 998) := by
    ext n
    simp 
    constructor
    · -- Assume h: ∃ r, 0 < r < 1 ∧ r.num = n ∧ ∃ k, r = k / 999.
      rintro ⟨r, hr1, hr2, h3, k, hk⟩ 
      have h4 : (k : ℚ) / 999 = r := by
        linarith [hk, hr1, hr2]
      have h5 : ( (k : ℚ) / 999).num = r.num := by 
        rw [h4]
      rw [show r.num = (n : ℤ) by linarith [h3]] at h5 
      have h8 : k ≤ 998 := by 
        by_contra h9 
        push_neg at h9
        have h10 : (k : ℚ) ≥ (999 : ℚ) := by 
          exact_mod_cast (show k ≥ 999 by omega)
        have h100 : (k : ℚ) / 999 ≥ (1 : ℚ) := by 
          have : (k : ℚ) ≥ (999 : ℚ) := by 
            linarith [h10]
          have h999_pos : (999 : ℚ) > (0 : ℚ) := by norm_num 
          apply (le_div_iff₀ h999_pos).mpr 
          linarith
        have h105 : r < (1 : ℚ) := hr2 
        nlinarith [show (k : ℚ) / 999 ≤ r by linarith [hk], h100, hr2]
      have h10 : k ≥ 1 := by 
        by_contra h11 
        push_neg at h11 
        have h12 : k = 0 := by 
          omega 
        have hk0 : (k : ℚ) = (0 : ℚ) := by 
          rw [show k = 0 by omega] 
          all_goals norm_num 
        rw [hk0] at h4 
        have hr1' : r > (0 : ℚ) := hr1 
        nlinarith 
      refine ⟨k, ⟨by omega, by omega⟩, by 
        have : ( (k : ℚ) / 999).num = (n : ℤ) := by 
          linarith [h5] 
        have h6 : ( (k : ℚ) / 999).num.natAbs = n := by 
          omega 
        omega 
      ⟩ 
    · -- Assume h: ∃ k ∈ Finset.Icc 1 998, (k : ℚ) / 999).num.natAbs = n.
      rintro ⟨k, ⟨hk1, hk2⟩, h⟩ 
      use (k : ℚ) / 999 
      constructor
      · -- Show 0 < r 
        have hk3 : (k : ℚ) > 0 := by 
          exact_mod_cast (show k > 0 by omega)
        have hk4 : (999 : ℚ) > 0 := by norm_num 
        positivity 
      constructor 
      · -- Show r < (1 : ℚ) 
        have h1 : (k : ℚ) < (999 : ℚ) := by 
          exact_mod_cast (show k < 999 by omega)
        have hk4 : (999 : ℚ) > (0 : ℚ) := by norm_num 
        apply (div_lt_iff₀ hk4).mpr 
        linarith 
      constructor
      · -- Show r's reduced form's numerator = n 
        have hk4 : (k : ℚ) > 0 := by 
          exact_mod_cast (show k > 0 by omega)
        have hk5 : (k : ℚ) / 999 > 0 := by 
          positivity
        have h6 : ( (k : ℚ) / 999).num > 0 := by 
          apply Rat.num_pos.mpr 
          linarith
        have h7 : ( (k : ℚ) / 999).num.natAbs = ( (k : ℚ) / 999).num := by
          omega 
        have h8 : ( (k : ℚ) / 999).num = (n : ℤ) := by 
          omega 
        omega
      · -- Show ∃ k : ℕ, r = k / 999 
        refine ⟨k, by simp⟩ 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide