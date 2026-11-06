import Mathlib

open Nat Finset

theorem number_theory_637458 (M : ℕ) :
  multiplicity (24 : ℕ) (M !) =
  min ((⌊(1 / 3 : ℚ) * ∑' j : ℕ, (M / 2 ^ (j + 1))⌋₊) : ℕ)
    (∑' j : ℕ, (M / 3 ^ (j + 1)) : ℕ) := by 
  have h1 : emultiplicity (24 : ℕ) (M !) =
  min ((⌊(1 / 3 : ℚ) * ∑' j : ℕ, (M / 2 ^ (j + 1))⌋₊) : ℕ)
    (∑' j : ℕ, (M / 3 ^ (j + 1)) : ℕ) := by 
    have hprime1 : Nat.Prime 2 := by 
      norm_num 
    have hprime2 : Nat.Prime 3 := by
      norm_num
    have eq1 : ∑' (j : ℕ), M / 3 ^ (j + 1) = padicValNat 3 (M !)  := by 
      let b := Nat.log 3 M + 1 
      have le1 : Nat.log 3 M < b := by 
        unfold b
        simp
      have bge : b ≥ 1 := by 
        omega
      -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), here p is 5
      obtain aux1 := padicValNat_factorial le1
      rw [aux1]
      -- prove the following two sum is equal using sum_nbij' 
      have aux2 : ∑ i ∈ Finset.Ico 1 b, M / 3 ^ i = ∑ i ∈ Ico 0 (b - 1), M / 3 ^ (i + 1) := by 
        let t : ℕ → ℕ := fun n => n + 1
        let s : ℕ → ℕ := fun n => n - 1
        refine (sum_nbij' s t ?_ ?_ ?_ ?_ ?_)
        · unfold s
          simp
          omega
        · unfold t
          simp
          omega
        · unfold s t 
          simp
          omega
        · unfold s t 
          simp 
        · unfold s
          simp
          intro a ha1 ha2 
          rw [show a - 1 + 1 = a by omega]
      rw [aux2]
      refine tsum_eq_sum ?_
      simp
      intro i hi
      refine lt_pow_of_log_lt ?_ ?_
      linarith
      linarith
    have eq2 : (∑' (j : ℕ), M / 2 ^ (j + 1)) = padicValNat 2 (M !) := by 
      let b := Nat.log 2 M + 1 
      have le1 : Nat.log 2 M < b := by 
        unfold b
        simp
      have bge : b ≥ 1 := by 
        omega
      -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), here p is 5
      obtain aux1 := padicValNat_factorial le1
      rw [aux1]
      -- prove the following two sum is equal using sum_nbij' 
      have aux2 : ∑ i ∈ Finset.Ico 1 b, M / 2 ^ i = ∑ i ∈ Ico 0 (b - 1), M / 2 ^ (i + 1) := by 
        let t : ℕ → ℕ := fun n => n + 1
        let s : ℕ → ℕ := fun n => n - 1
        refine (sum_nbij' s t ?_ ?_ ?_ ?_ ?_)
        · unfold s
          simp
          omega
        · unfold t
          simp
          omega
        · unfold s t 
          simp
          omega
        · unfold s t 
          simp 
        · unfold s
          simp
          intro a ha1 ha2 
          rw [show a - 1 + 1 = a by omega]
      rw [aux2]
      refine tsum_eq_sum ?_
      simp
      intro i hi
      refine lt_pow_of_log_lt ?_ ?_
      linarith
      linarith
    refine (emultiplicity_eq_coe).mpr ?_ 
    constructor 
    · 
      rw [show 24 = 2 ^ 3 * 3 by norm_num, mul_pow, ←pow_mul]
      have dvd1 : 2 ^ padicValNat 2 (M !) ∣ M ! := by 
        exact pow_padicValNat_dvd
      have dvd2 : 2 ^ (3 * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1)))  ∣ 2 ^  padicValNat 2 (M !) := by 
        have le_aux : (3 * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1)))  ≤   padicValNat 2 (M !) := by 
          have aux : ((3 : ℚ) * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1)))  ≤   padicValNat 2 (M !) := by 
            calc 
              _ ≤ 3 * (1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))) := by 
                apply mul_le_mul_of_nonneg_left
                have ineq : ((⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1))) ≤ (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ : ℚ) := by 
                  norm_cast
                  apply min_le_left
                have ineq2 : 1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1)) ≥ ⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ := by 
                  apply floor_le 
                  positivity
                norm_num at ineq2
                linarith
                linarith
              _ = _ := by 
                field_simp
                rw [eq2]
          norm_cast at aux
        exact pow_dvd_pow_iff_le_right'.mpr le_aux
      have dvd3 : 3 ^ padicValNat 3 (M !) ∣ M ! := by 
        exact pow_padicValNat_dvd
      have dvd4 : 3 ^ ((⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1)))  ∣ 3 ^  padicValNat 3 (M !) := by 
        have le_aux : ((⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1)))  ≤  padicValNat 3 (M !)  := by 
          rw [eq1]
          simp
        exact pow_dvd_pow_iff_le_right'.mpr le_aux
      obtain dvd_aux1 := dvd_trans dvd2 dvd1 
      obtain dvd_aux2 := dvd_trans dvd4 dvd3
      zify at dvd_aux1 dvd_aux2 ⊢ 
      refine IsCoprime.mul_dvd ?_ dvd_aux1 dvd_aux2
      refine IsCoprime.pow ?_
      norm_num
    · 
      have prime2 : Fact (Nat.Prime 2) := by 
        exact fact_prime_two
      have prime3 : Fact (Nat.Prime 3) := by
        exact fact_prime_three
      have neq : M ! ≠ 0 := by 
        exact factorial_ne_zero M
      by_cases h1 : ⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1) = ⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊
      rw [h1]
      by_contra hc 
      have dvd1 : 2 ^ (3 * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ + 1)) ∣ 
        24 ^ ((⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ + 1)) := by 
        rw [show 24 = 2 ^ 3 * 3 by norm_num, mul_pow, ←pow_mul]
        apply Nat.dvd_mul_right
      have dvd2 : 2 ^ (3 * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ + 1)) ∣ M ! := by 
        exact dvd_trans dvd1 hc
      obtain h2 := padicValNat_dvd_iff_le neq |>.mp dvd2
      rw [←eq2] at h2
      have aux1 : ⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ > 
        1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1)) - 1 := by 
        apply sub_one_lt_floor
      have aux2 : (3 : ℚ) * (⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ + 1) > ∑' (j : ℕ), M / 2 ^ (j + 1) := by 
        calc 
          _ > (3 : ℚ) * (1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1)) - 1 + 1) := by 
            linarith
          _ = _ := by 
            ring
      norm_cast at aux2
      linarith
      have h2 : ⌊1 / (3 : ℚ) * ↑(∑' (j : ℕ), M / 2 ^ (j + 1))⌋₊ ⊓ ∑' (j : ℕ), M / 3 ^ (j + 1) = ∑' (j : ℕ), M / 3 ^ (j + 1) := by 
        simp at h1
        refine Nat.min_eq_right ?_
        simp
        linarith
      rw [h2]
      by_contra hc 
      rw [eq1] at hc 
      have dvd1 : 3 ^ (padicValNat 3 (M !) + 1) ∣ M ! := by 
        have aux1 :  3 ^ (padicValNat 3 (M !) + 1) ∣ 24  ^ (padicValNat 3 (M !) + 1) := by
          rw [show 24 = 3 * 8 by norm_num, mul_pow]
          apply Nat.dvd_mul_right
        exact Nat.dvd_trans aux1 hc
      obtain h2 := padicValNat_dvd_iff_le neq |>.mp dvd1
      linarith
  exact multiplicity_eq_of_emultiplicity_eq_some h1