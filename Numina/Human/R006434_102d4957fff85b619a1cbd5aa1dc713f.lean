import Mathlib

open Nat Finset

theorem number_theory_637024 (N : ℕ) (hN : N > 0): 
  multiplicity 10 (N !) = ∑' (k : ℕ), N / (5 ^ (k + 1)) := by 
  -- Nat.Prime.emultiplicity_factorial
  have h1 : emultiplicity 10 (N !) = ∑' (k : ℕ), N / (5 ^ (k + 1))  := by 
    have prime1 : Nat.Prime 5 := by norm_num
    let b := Nat.log 5 N + 1 
    have le1 : Nat.log 5 N < b := by 
      unfold b
      simp
    have bge : b ≥ 1 := by 
      omega
    -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), here p is 5
    obtain aux1 := Nat.Prime.emultiplicity_factorial prime1 le1
    -- prove the following two sum is equal using sum_nbij' 
    have aux2 : ∑ i ∈ Finset.Ico 1 b, N / 5 ^ i = ∑ i ∈ Ico 0 (b - 1), N / 5 ^ (i + 1) := by 
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
    let c := log 2 N + 1
    have prime2 : Nat.Prime 2 := by norm_num
    have le2 : log 2 N < c := by 
      unfold c
      simp
    -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), here p is 2
    obtain aux2' := Nat.Prime.emultiplicity_factorial prime2 le2
    have ge_aux : (∑ i ∈ Ico 1 c, N / 2 ^ i) ≥ (∑ i ∈ Ico 1 b, N / 5 ^ i) := by 
      have aux3 : (∑ i ∈ Ico 1 b, N / 5 ^ i) ≤ (∑ i ∈ Ico 1 c, N / 5 ^ i) := by 
        apply Finset.sum_le_sum_of_subset
        refine Ico_subset_Ico_right ?_
        unfold b c
        simp 
        refine log_anti_left ?_ ?_
        linarith
        linarith
      have aux4 : (∑ i ∈ Ico 1 c, N / 5 ^ i) ≤ (∑ i ∈ Ico 1 c, N / 2 ^ i) := by   
        refine sum_le_sum ?_
        intro i hi
        refine Nat.div_le_div_left ?_ ?_
        refine pow_le_pow_of_le_left ?_ i
        linarith
        positivity
      linarith
    
    have ge_aux2 : ((∑ i ∈ Ico 1 c, N / 2 ^ i : ℕ): ℕ∞) ≥ ∑ i ∈ Ico 1 b, N / 5 ^ i := by 
      norm_cast
    
    have eq1 : (∑' (k : ℕ), N / 5 ^ (k + 1)) = (∑ i ∈ Finset.Ico 1 b, N / 5 ^ i) := by 
      rw [aux2]
      refine tsum_eq_sum ?_
      intro n hn1
      simp at hn1
      by_contra hc
      have ge1 : N / 5 ^ (n + 1) ≥ 1 := by 
        exact one_le_iff_ne_zero.mpr hc
      have Nge : N ≥ 5 ^ (n + 1) := by
        refine (Nat.one_le_div_iff ?_).mp ge1 
        positivity
      have hcontra : log 5 N ≥ n + 1 := by 
        refine (pow_le_iff_le_log ?_ ?_).mp Nge
        linarith
        linarith
      linarith
    -- use the result that emultiplicity a b = ↑k, if  ¬a ^ (k + 1) ∣ b
    apply emultiplicity_eq_of_dvd_of_not_dvd
    · -- prove that 10 ^ ∑' (k : ℕ), N / 5 ^ (k + 1) ∣ N !, since 2 ^ ∑' (k : ℕ), N / 5 ^ (k + 1) ∣ N ! and 5 ^ ∑' (k : ℕ), N / 5 ^ (k + 1) ∣ N !, and 2 and 5 are coprime.
      rw [show 10 = 5 * 2 by norm_num, mul_pow]
      have dvd2 : 2 ^ ∑' (k : ℕ), N / 5 ^ (k + 1) ∣ N ! := by 
        rw [←aux2'] at ge_aux2 
        rw [eq1]
        refine pow_dvd_iff_le_emultiplicity.mpr ?_ 
        exact ge_aux2
      have dvd3 : 5 ^ ∑' (k : ℕ), N / 5 ^ (k + 1) ∣ N ! := by 
        rw [eq1]
        refine pow_dvd_iff_le_emultiplicity.mpr ?_ 
        rw [aux1]
      refine Coprime.mul_dvd_of_dvd_of_dvd ?_ dvd3 dvd2
      exact Coprime.pow (∑' (k : ℕ), N / 5 ^ (k + 1)) (∑' (k : ℕ), N / 5 ^ (k + 1)) rfl
    · -- prove that ¬10 ^ (∑' (k : ℕ), N / 5 ^ (k + 1) + 1) ∣ N !, since emultiplicity 10 N! = ∑' (k : ℕ), N / 5 ^ (k + 1)
      rw [show 10 = 5 * 2 by norm_num, mul_pow]
      by_contra hc
      have dvd1 : 5 ^ (∑' (k : ℕ), N / 5 ^ (k + 1) + 1) ∣ 5 ^ (∑' (k : ℕ), N / 5 ^ (k + 1) + 1) * 2 ^ (∑' (k : ℕ), N / 5 ^ (k + 1) + 1) := by 
        simp
      have dvd2 : 5 ^ (∑' (k : ℕ), N / 5 ^ (k + 1) + 1) ∣ N ! := by
        exact Nat.dvd_trans dvd1 hc
      obtain aux3 := le_emultiplicity_of_pow_dvd dvd2
      rw [aux1] at aux3
      norm_cast at aux3
      linarith
  exact multiplicity_eq_of_emultiplicity_eq_some h1