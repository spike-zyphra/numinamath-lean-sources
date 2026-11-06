import Mathlib

open Nat Finset

theorem number_theory_640828 (p n : ℕ) (hp : Nat.Prime p) :
  (∏ i ∈ Ico 1 p, (n + i - 1)) ≡ if n ≡ 1 [ZMOD p] then p - 1 else 0 [ZMOD p] := by 
  by_cases hp2 : p = 2
  · -- the prime number p = 2 
    rw [hp2]
    simp
    by_cases hn1 : ↑n ≡ 1 [ZMOD 2] 
    · rw [if_pos hn1]
      exact hn1
    · rw [if_neg hn1]
      unfold Int.ModEq
      simp
      norm_cast
      unfold Int.ModEq at hn1
      simp at hn1
      norm_cast at hn1
  have pgt2 : p > 2 := by 
      refine two_lt_of_ne ?_ ?_ hp2
      exact Nat.Prime.ne_zero hp
      exact Nat.Prime.ne_one hp
  -- the case p ≥ 3
  by_cases h₀ : n ≡ 1 [ZMOD p]
  · -- the case n ≡ 1 [ZMOD p]
    rw [if_pos h₀]
    calc 
      _ ≡ ∏ i ∈ Ico 1 p, i [ZMOD p] := by 
        -- have aux : ∏ i ∈ Ico 1 p, (↑n + ↑i) % (p : ℤ) ≡ ∏ i ∈ Ico 1 p, ↑i % (p : ℤ) := by 
        --   have aux1 : ∏ i ∈ Ico 1 p, (↑n + ↑i) % p ≡ ∏ i ∈ Ico 1 p, ↑i
        unfold Int.ModEq
        rw [prod_int_mod]
        conv => 
          rhs
          rw [prod_int_mod]
        
        have aux : (∏ i ∈ Ico 1 p, (↑n + ↑i - 1) % (p : ℤ)) = ∏ i ∈ Ico 1 p, (↑i % (p : ℤ)) := by 
          apply prod_congr rfl
          intro x hx
          obtain aux1 := Int.ModEq.dvd (Int.ModEq.symm h₀)
          obtain ⟨m, hm⟩ := aux1
          have neq : (n : ℤ) = 1 + m * p := by linarith
          rw [neq]
          apply Int.modEq_of_dvd
          ring_nf
          simp
        rw [aux]
      _ ≡ -1 [ZMOD p] := by 
        have aux : Fact (Nat.Prime p) := by 
          exact { out := hp }
        obtain h1 :=  @ZMod.prod_Ico_one_prime p aux
        refine (ZMod.intCast_eq_intCast_iff _ _ _ ).mp ?_
        norm_num
      _ ≡ p - 1 [ZMOD p] := by
        apply Int.modEq_of_dvd
        simp
  · -- the case ¬ n ≡ 1 [ZMOD p]
    rw [if_neg h₀]
    unfold Int.ModEq
    rw [prod_int_mod]
    have aux : (∏ i ∈ Ico 1 p, (↑n + ↑i - 1) % (p : ℤ))  = 
      0 := by 
      refine prod_eq_zero_iff.mpr ?_
      by_cases nmod : n ≡ 0 [ZMOD p]
      · 
        use 1
        constructor
        · simp
          exact Prime.one_lt hp
        · ring_nf
          exact nmod
      · -- the cases ¬ n ≡ 0 [ZMOD p] ∧ ¬ n ≡ 1 [ZMOD p]
        use (p + 1 - n % p)
        constructor
        · 
          simp
          constructor
          · rw [add_comm]
            have aux1 : 1 + p - n % p = 1 + (p - n % p) := by 
              have pge : p ≥ n % p := by 
                have pgt : p > n % p := by 
                  refine mod_lt n ?_
                  exact Prime.pos hp
                linarith
              omega
            rw [aux1]
            linarith
          · 
            
            have nmodge : (n : ℤ) % p ≥ 2 := by 
              have neq1 : (n : ℤ) % p ≠ 1 := by
                unfold Int.ModEq at h₀
                have aux : 1 % (p : ℤ) = 1 := by 
                  refine Int.emod_eq_of_lt ?_ ?_
                  linarith
                  
                  linarith
                rw [aux] at h₀
                exact h₀
              have neq2 : (n : ℤ) % p ≠ 0 := by
                unfold Int.ModEq at nmod
                simp at nmod
                simp
                exact nmod
              omega
            norm_cast at nmodge
            omega
        · 
          have cast1 : ↑(p + 1 - n % p : ℕ) = ((p : ℤ) + 1 - n % p) := by 
            have aux1 : 1 + p - n % p = 1 + (p - n % p) := by 
              have pge : p ≥ n % p := by 
                have pgt : p > n % p := by 
                  refine mod_lt n ?_
                  exact Prime.pos hp
                linarith
              omega
            rw [add_comm, aux1]
            norm_num
            have cast_aux : ↑(p - n % p : ℕ) = ((p : ℤ) - n % p) := by 
              have pge : p ≥ n % p := by 
                have pgt : p > n % p := by 
                  refine mod_lt n ?_
                  exact Prime.pos hp
                linarith
              omega
            rw [cast_aux]
            ring_nf
          rw [cast1]
          ring_nf
          have dvd1 : (p : ℤ) ∣ ((n : ℤ) - ↑n % p) := by 
            exact Int.dvd_sub_of_emod_eq rfl
          have aux1 : (n : ℤ) + (↑p - ↑n % ↑p) = p + (n - n % p) := by 
            ring
          refine Int.dvd_iff_emod_eq_zero.mp ?_
          rw [aux1]
          exact dvd_add_self_left.mpr dvd1
    rw [aux]