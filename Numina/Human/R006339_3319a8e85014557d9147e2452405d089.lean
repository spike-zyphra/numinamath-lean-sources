import Mathlib

open Nat Finset

-- def a auxillary function to define the ⌊1 / a * ∑' k, N / p ^ k⌋₊, where a is the padicValNat p M


noncomputable def f (M : ℕ) (N : ℕ) : ℕ → ℕ := fun p => ⌊ (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))⌋₊ 

/- Let $N$ be a non-negative natural number and $M$ be a natural number greater than 1. Let the prime factorization of $M$ be $M = p_1^{a_1} p_2^{a_2} \dots p_r^{a_r}$, where $p_i$ are distinct prime numbers and $a_i \ge 1$ for all $i=1, \dots, r$. Determine the multiplicity of $M$ in $N!$. Show that this multiplicity is equal to $\min_{1 \le i \le r} \left\{ \left\lfloor \frac{1}{a_i} \sum_{k=1}^{\infty} \left\lfloor \frac{N}{p_i^k} \right\rfloor \right\rfloor \right\}$.-/
theorem number_theory_636075 {N : ℕ} {M : ℕ} (hM : M > 1) :
  multiplicity M (N !) = min' (image (f M N) M.primeFactors) (image_nonempty.mpr (nonempty_primeFactors.mpr hM)):= by 
  -- for notation simplicity, denote this number to be 
  let n := min' (image (f M N) M.primeFactors) (image_nonempty.mpr (nonempty_primeFactors.mpr hM))
  
  have h1 : emultiplicity M (N !) = min' (image (f M N) M.primeFactors) (image_nonempty.mpr (nonempty_primeFactors.mpr hM)) := by 
    refine (emultiplicity_eq_coe).mpr ?_ 
    constructor 
    · 
      refine (Nat.factorization_prime_le_iff_dvd ?_ ?_ ).mp ?_ 
      positivity
      exact factorial_ne_zero N
      intro p hp
      by_cases hp1 : p ∈ M.primeFactors
      · 
        rw [factorization_pow]
        simp
        have eq1 : M.factorization p = padicValNat p M := by 
          exact factorization_def M hp
        rw [eq1]
        -- minimal of a finite set is less than any element of this finite set.
        have min_le_aux : n ≤ ⌊ (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))⌋₊  := by 
          unfold n f 
          apply min'_le
          simp 
          use p
          constructor 
          · constructor
            exact hp
            constructor 
            exact dvd_of_mem_primeFactors hp1
            linarith
          rfl
        have ineq1 : ⌊ (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))⌋₊  ≤ 
          (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1))) := by 
          apply floor_le 
          positivity 
        have factprime : Fact (Nat.Prime p) := by 
          exact { out := hp }
        -- use the Legendre formula to get the (N !).factorization p = ∑' (k : ℕ), N / (p ^ (k + 1)
        have eq_aux :  (N !).factorization p = ∑' (k : ℕ), N / (p ^ (k + 1)) := by
          let b := Nat.log p N + 1 
          have le1 : Nat.log p N < b := by 
            unfold b
            simp
          have bge : b ≥ 1 := by 
            omega
          -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), 
          obtain aux1 := Nat.Prime.emultiplicity_factorial hp le1
          -- prove the following two sum is equal using sum_nbij' 
          have aux2 : ∑ i ∈ Finset.Ico 1 b, N / p ^ i = ∑ i ∈ Ico 0 (b - 1), N / p ^ (i + 1) := by 
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
          have aux3 : (N !).factorization p = multiplicity p (N !) := by 
            refine Eq.symm (multiplicity_eq_factorization hp ?_)
            exact factorial_ne_zero N
          rw [aux3]
          refine multiplicity_eq_of_emultiplicity_eq_some ?_
          rw [aux1, aux2]
          norm_cast
          apply Eq.symm
          apply tsum_eq_sum
          simp
          intro i hi
          right
          refine lt_pow_of_log_lt ?_ ?_
          exact Prime.one_lt hp
          linarith
        have aux : (n : ℚ) * padicValNat p M ≤ ((N !).factorization p : ℚ) := by  
          calc 
            _ ≤ ⌊ (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))⌋₊  * (padicValNat p M : ℚ) := by 
              apply mul_le_mul
              norm_cast
              simp
              norm_cast
              linarith
              positivity
            _ ≤ (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1))) * (padicValNat p M : ℚ) := by 
              apply mul_le_mul
              exact ineq1
              simp
              norm_cast
              linarith
              positivity
            _ = (∑' (k : ℕ), N / (p ^ (k + 1))) := by 
              have pos : (padicValNat p M) > 0 := by 
                refine zero_lt_of_ne_zero ?_
                refine (dvd_iff_padicValNat_ne_zero ?_).mp ?_
                linarith
                exact dvd_of_mem_primeFactors hp1
              field_simp
            _ = _ := by 
              rw [eq_aux]
        norm_cast at aux
      -- if p is a prime factor of M, then the left hand side of goal is zero
      have eq0 : (M ^ n).factorization p = 0 := by 
        rw [factorization_pow]
        simp 
        right 
        exact Finsupp.not_mem_support_iff.mp hp1
      rw [eq0]
      linarith
    -- now we prove the second part of the theorem `¬M ^ ((image (f M N) M.primeFactors).min' ⋯ + 1) ∣ N !`
    · 
      -- the minimal of the finite set is a element in this finite set
      have mem_aux : n ∈ (image (f M N) M.primeFactors) := by 
        apply min'_mem 
      simp at mem_aux
      obtain ⟨p, hp, h1⟩ := mem_aux
      obtain ⟨hp1, hp2, hp3⟩ := hp
      -- assume that  M ^ ((image (f M N) M.primeFactors).min' ⋯ + 1) ∣ N!
      by_contra hc
      have pdvd : (p ^ (padicValNat p M)) ^ (n + 1) ∣ M ^ (n + 1) := by 
        refine pow_dvd_pow_of_dvd ?_ (n + 1)
        exact pow_padicValNat_dvd
      have pdvd2 : (p ^ (padicValNat p M)) ^ (n + 1) ∣ N ! := by 
        exact Nat.dvd_trans pdvd hc
      rw [←pow_mul] at pdvd2
      have neq : N ! ≠ 0 := by 
        exact factorial_ne_zero N
      have factprime : Fact (Nat.Prime p) := by
        exact { out := hp1 }
      obtain h2 := padicValNat_dvd_iff_le neq |>.mp pdvd2
      have eq_aux : padicValNat p M * (n + 1) > padicValNat p (N !) := by 
        unfold f at h1
        have ineq1 : (padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1))) - 1 
          < ⌊(padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))⌋₊ := by 
          apply sub_one_lt_floor
        have aux : (padicValNat p M : ℚ) * (n + 1) > padicValNat p N ! := by 
          calc 
            _ > (padicValNat p M : ℚ) * ((padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))) := by 
              have aux : ((n : ℚ) + 1) > ((padicValNat p M : ℚ)⁻¹ * (∑' (k : ℕ), N / (p ^ (k + 1)))) := by 
                rw [←h1]
                linarith
              have pos : (padicValNat p M : ℚ) > 0 := by 
                norm_cast
                refine zero_lt_of_ne_zero ?_
                exact (dvd_iff_padicValNat_ne_zero hp3).mp hp2
              apply mul_lt_mul_of_pos_left aux pos
            _ = _ := by 
              have eq_aux : padicValNat p N ! = ∑' (k : ℕ), N / (p ^ (k + 1)) := by
                let b := Nat.log p N + 1 
                have le1 : Nat.log p N < b := by 
                  unfold b
                  simp
                have bge : b ≥ 1 := by 
                  omega
                -- use the Legendre formula, we can get that emultiplicity p n ! = ↑(∑ i ∈ Ico 1 b, n / p ^ i), 
                obtain aux1 := padicValNat_factorial le1
                -- prove the following two sum is equal using sum_nbij' 
                have aux2 : ∑ i ∈ Finset.Ico 1 b, N / p ^ i = ∑ i ∈ Ico 0 (b - 1), N / p ^ (i + 1) := by 
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
                rw [aux1, aux2]
                apply Eq.symm
                apply tsum_eq_sum
                simp
                intro i hi
                right
                refine lt_pow_of_log_lt ?_ ?_
                exact Prime.one_lt hp1
                linarith
              rw [eq_aux]
              have neq : (padicValNat p M) ≠ 0 := by 
                exact (dvd_iff_padicValNat_ne_zero hp3).mp hp2
              field_simp
        norm_cast at aux
      linarith
  exact multiplicity_eq_of_emultiplicity_eq_some h1