import Mathlib

open Finset Nat

theorem number_theory_636750 {b : ℕ} (hb : Even b)
  (k m : ℕ) (hk : k > 0) (hm : m > 0) (hkm : m > k) :
  Nat.Coprime (fib (b ^ 2 ^ k + 1)) (fib (b ^ 2 ^ m + 1)) := by
  -- first prove that gcd (b ^ 2 ^ k + 1) (b ^ 2 ^ m + 1) = 1
  have h0 : Nat.gcd (b ^ 2 ^ k + 1) (b ^ 2 ^ m + 1) = 1:= by 
    by_contra hc
    have aux1 : ∃ p, Nat.Prime p ∧ p ∣ Nat.gcd (b ^ 2 ^ k + 1) (b ^ 2 ^ m + 1) := by
      exact exists_prime_and_dvd hc
    obtain ⟨p, hp1, hpdvd⟩ := aux1
    have aux2 : b ^ 2 ^ m = (b ^ 2 ^ k) ^ 2 ^ (m - k) := by 
      rw [←pow_mul]
      have aux3 : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by 
        have aux4 : m = k + (m - k) := by 
          omega
        rw [←pow_add, ←aux4]
      rw [aux3]
    have pdvd1 : p ∣ (b ^ 2 ^ k + 1) := by 
      have aux : (b ^ 2 ^ k + 1).gcd (b ^ 2 ^ m + 1) ∣ (b ^ 2 ^ k + 1) := by 
        exact Nat.gcd_dvd_left (b ^ 2 ^ k + 1) (b ^ 2 ^ m + 1)
      exact Nat.dvd_trans hpdvd aux
    have pdvd2 : p ∣ (b ^ 2 ^ m + 1) := by 
      have aux : (b ^ 2 ^ k + 1).gcd (b ^ 2 ^ m + 1) ∣ (b ^ 2 ^ m + 1) := by 
        exact Nat.gcd_dvd_right (b ^ 2 ^ k + 1) (b ^ 2 ^ m + 1)
      exact Nat.dvd_trans hpdvd aux
    zify at pdvd1 pdvd2
    have modeq1 : b ^ 2 ^ k ≡ -1 [ZMOD p] := by 
      apply Int.ModEq.symm 
      apply Int.modEq_of_dvd
      simp
      exact pdvd1
    have modeq2 : b ^ 2 ^ m ≡ -1 [ZMOD p] := by 
      apply Int.ModEq.symm 
      apply Int.modEq_of_dvd
      simp
      exact pdvd2
    have modeq3 : - 1 ≡ 1 [ZMOD p] := by 
      calc 
        _ ≡  b ^ 2 ^ m [ZMOD p] := by 
          exact id (Int.ModEq.symm modeq2)
        _ ≡ (-1) ^ 2 ^(m - k) [ZMOD p] := by 
          zify at aux2
          rw [aux2]
          exact Int.ModEq.pow (2 ^ (m - k)) modeq1
        _ ≡ 1 [ZMOD p] := by 
          congr
          refine Even.neg_one_pow ?_
          refine (even_pow' ?_).mpr ?_
          have msubk : m - k > 0 := by 
            omega
          linarith
          simp
    obtain pdvd3 := Int.ModEq.dvd modeq3
    simp at pdvd3
    norm_cast at pdvd3
    have peq2 : p = 2 := by 
      have prime2 : Nat.Prime 2 := by 
        norm_num
      exact (Nat.prime_dvd_prime_iff_eq hp1 prime2).mp pdvd3
    norm_cast at pdvd1
    have pdvd4 : p ∣ b ^ 2 ^ k := by 
      have pdvdb : p ∣ b := by 
        rw [peq2]
        exact even_iff_two_dvd.mp hb
      refine Dvd.dvd.pow pdvdb ?_
      positivity
    have pdvd5 : p ∣ 1 := by 
      zify at pdvd1 pdvd4 ⊢
      have eq1 : (1 : ℤ) = b ^ 2 ^ k + 1 - b ^ 2 ^ k := by 
        ring
      rw [eq1]
      exact Int.dvd_sub pdvd1 pdvd4
    rw [peq2] at pdvd5
    norm_num at pdvd5
  -- then use the result that gcd (fib m) (fib n) = fib (gcd m n)
  have h1 : Nat.gcd (fib (b ^ 2 ^ k + 1)) (fib (b ^ 2 ^ m + 1)) = 1 := by
    rw [←fib_gcd, h0]
    rfl
  exact h1