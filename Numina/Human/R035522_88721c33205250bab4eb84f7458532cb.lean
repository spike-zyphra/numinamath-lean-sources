import Mathlib
open Real

theorem number_theory_142888 
(p :ℕ) (h :  Nat.Prime p ∧ 10^17 + 1 ≤ p ∧ p ≤ 10^17 + 9) : p = 10^17+3 := by

  have even_or_five_ending_composite (n : ℕ) (h₁ : n ≥ 10) (h₂ : (n % 10)% 2 = 0  ∨ n % 10 = 5) : ¬ Nat.Prime n := by
    intro h₃
    have h₄ := Nat.Prime.eq_one_or_self_of_dvd h₃ 2
    have h₅ := Nat.Prime.eq_one_or_self_of_dvd h₃ 5
    have h₆ : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
      omega
    rcases h₆ with (h₆ | h₆ | h₆ | h₆ | h₆ | h₆ | h₆ | h₆ | h₆ | h₆) <;>
      (try omega) 
  have h3 : p = 10^17 + 3 := by
    
    have h4 : p ≥ 10^17 + 1 := h.2.1
    have h5 : p ≤ 10^17 + 9 := h.2.2
    
    have h6 : p = 10^17 + 1 ∨ p = 10^17 + 2 ∨ p = 10^17 + 3 ∨ p = 10^17 + 4 ∨ p = 10^17 + 5 ∨ p = 10^17 + 6 ∨ p = 10^17 + 7 ∨ p = 10^17 + 8 ∨ p = 10^17 + 9 := by
      omega

    have not_p_eq_power_plus_even (k : ℕ) (hk : k % 2 = 0 ∨ k %5 = 0) : ¬ p = 10^17 + k := by
      by_contra h01
      have h04 : p ≥ 10 := by 
        norm_num at h01 ⊢ 
        omega
      have h02 : (p % 10)% 2 = 0  ∨ p % 10 = 5 := by 
        norm_num at h01 ⊢ 
        omega
      have h03 :  ¬ Nat.Prime (p) := by
        apply even_or_five_ending_composite (p) h04 h02
      have h06 : Nat.Prime (p) := by simpa [h4] using h.1
      exact h03 h06

    have h61 : ¬ p = 10^17 + 9 := by 
      by_contra hp1
      have hh : p ≡ 0 [ZMOD 7] := by
        have h₁ : p = 10 * 100^8 + 9 := by
          norm_num at hp1 ⊢
          omega
        rw [h₁]
        have h₂ : (10 * 100^8 + 9 : ℤ) ≡ (3 * 2^8 + 2 : ℤ) [ZMOD 7] := by
          norm_num [Int.ModEq, pow_succ]
        have h₃ : (3 * 2^8 + 2 : ℤ) ≡ 0 [ZMOD 7] := by
          norm_num [Int.ModEq, pow_succ]
        have h₄ : (10 * 100^8 + 9 : ℤ) ≡ 0 [ZMOD 7] := by
          calc
            (10 * 100^8 + 9 : ℤ) ≡ (3 * 2^8 + 2 : ℤ) [ZMOD 7] := h₂
            _ ≡ 0 [ZMOD 7] := h₃
        exact h₄
      have h₃ : (7 : ℤ) ∣ p := by
        rw [Int.dvd_iff_emod_eq_zero]
        rw [Int.ModEq] at hh
        norm_num [Int.emod_eq_of_lt] at hh ⊢
        omega
      have h₃0 : (7 : ℕ) ∣ p := by
        norm_cast at h₃ ⊢
      have h₄ : ¬ Nat.Prime p := by
        intro h
        have h₅ := h.eq_one_or_self_of_dvd 7 h₃0
        have h₆ : p ≠ 1 := by omega
        have h₇ : p = 7 := by omega
        omega
      have h06 : Nat.Prime (p) := by simpa [h4] using h.1
      exact h₄ h06
    have h62 : ¬ p = 10^17 + 2 := by apply not_p_eq_power_plus_even 2 (by norm_num)
      
    have h63 : ¬ p = 10^17 + 4 := by apply not_p_eq_power_plus_even 4 (by norm_num)

    have h64 : ¬ p = 10^17 + 5 := by apply not_p_eq_power_plus_even 5 (by norm_num)

    have h65 : ¬ p = 10^17 + 6 := by apply not_p_eq_power_plus_even 6 (by norm_num)

    have h66 : ¬ p = 10^17 + 7 := by 
      by_contra hp2
      have hh : p ≡ 0 [ZMOD 17] := by
        have h₁ : p = 10 * 100^8 + 7 := by
          norm_num at hp2 ⊢
          omega
        rw [h₁]
        have h₂ : (10 * 100^8 + 7 : ℤ) ≡ (10 * (-2)^8 + 7 : ℤ) [ZMOD 17] := by
          norm_num [Int.ModEq, pow_succ]
        have h₃ : (10 * (-2)^8 + 7 : ℤ) ≡ 0 [ZMOD 17] := by
          norm_num [Int.ModEq, pow_succ]
        have h₄ : (10 * 100^8 + 7 : ℤ) ≡ 0 [ZMOD 17] := by
          calc
            (10 * 100^8 + 7 : ℤ) ≡ (10 * (-2)^8 + 7 : ℤ) [ZMOD 17] := h₂
            _ ≡ 0 [ZMOD 17] := h₃
        exact h₄
      have h₃ : (17 : ℤ) ∣ p := by
        rw [Int.dvd_iff_emod_eq_zero]
        rw [Int.ModEq] at hh
        norm_num [Int.emod_eq_of_lt] at hh ⊢
        omega
      have h₃0 : (17 : ℕ) ∣ p := by
        norm_cast at h₃ ⊢
      have h₄ : ¬ Nat.Prime p := by
        intro h
        have h₅ := h.eq_one_or_self_of_dvd 17 h₃0
        have h₆ : p ≠ 1 := by omega
        have h₇ : p = 17 := by omega
        omega
      have h06 : Nat.Prime (p) := by simpa [h4] using h.1
      exact h₄ h06
    have h67 : ¬ p = 10^17 + 8 := by apply not_p_eq_power_plus_even 8 (by norm_num)  
    have h68 : ¬ p = 10^17 + 1 := by 
      by_contra hp2
      have hh : p ≡ 0 [ZMOD 11] := by
        have h₁ : p = 10^17 + 1 := hp2
        have h₂ : (10^17 + 1 : ℤ) ≡ ((-1)^17 + 1 : ℤ) [ZMOD 11] := by
          norm_num [Int.ModEq, pow_succ]
        have h₃ : ((-1)^17 + 1 : ℤ) ≡ 0 [ZMOD 11] := by
          norm_num [Int.ModEq, pow_succ]
        have h₄ : (10^17 + 1 : ℤ) ≡ 0 [ZMOD 11] := by
          calc
            (10^17 + 1 : ℤ) ≡ ((-1)^17 + 1 : ℤ) [ZMOD 11] := h₂
            _ ≡ 0 [ZMOD 11] := h₃
        have h₅ : (p : ℤ) ≡ 0 [ZMOD 11] := by
          rw [h₁]
          exact h₄
        exact h₅

      have h₃ : (11 : ℤ) ∣ p := by
        rw [Int.dvd_iff_emod_eq_zero]
        rw [Int.ModEq] at hh
        norm_num [Int.emod_eq_of_lt] at hh ⊢
        omega
      have h₃0 : (11 : ℕ) ∣ p := by
        norm_cast at h₃ ⊢
      have h₄ : ¬ Nat.Prime p := by
        intro h
        have h₅ := h.eq_one_or_self_of_dvd 11 h₃0
        have h₆ : p ≠ 1 := by omega
        have h₇ : p = 11 := by omega
        omega
      have h06 : Nat.Prime (p) := by simpa [h4] using h.1
      exact h₄ h06
    rcases h6 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- p = 10^17 + 1
      norm_num at h68
    · -- p = 10^17 + 2
      norm_num at h62
    · -- p = 10^17 + 3
      rfl
    · -- p = 10^17 + 4
      norm_num at h63
    · -- p = 10^17 + 5
      norm_num at h64
    · -- p = 10^17 + 6
      norm_num at h65

    · -- p = 10^17 + 7
      norm_num at h66

    · -- p = 10^17 + 8
      norm_num at h67

    · -- p = 10^17 + 9
      norm_num at h61
  exact h3

