import Mathlib

open Nat

theorem number_theory_638292 (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
  (hk : 0 < k) (h1 : a ∣ b^k) (h2 : b ∣ c^k) (h3 : c ∣ a^k) :
  a * b * c ∣ (a + b + c)^(k^2 + k + 1) := by
  refine (Nat.factorization_prime_le_iff_dvd ?_ ?_).mp ?_ 
  · positivity
  · positivity
  · intro p hp
    have hp1 : Fact (Nat.Prime p) := by 
      exact { out := hp }
    rw [factorization_def _ hp, factorization_def _ hp, 
      padicValNat.pow, padicValNat.mul, padicValNat.mul]

    · -- here we prove `padicValNat p a + padicValNat p b + padicValNat p c ≤ (k ^ 2 + k + 1) * padicValNat p (a + b + c)`
      have hle1 : padicValNat p a ≤ k * padicValNat p b := by
        rw [←padicValNat.pow, ←factorization_def _ hp, ← factorization_def _ hp]
        refine (Nat.factorization_prime_le_iff_dvd ?_ ?_).mpr h1 p hp
        repeat positivity
      have hle2 : padicValNat p b ≤ k * padicValNat p c := by
        rw [←padicValNat.pow, ←factorization_def _ hp, ← factorization_def _ hp]
        refine (Nat.factorization_prime_le_iff_dvd ?_ ?_).mpr h2 p hp
        repeat positivity
      have hle3 : padicValNat p c ≤ k * padicValNat p a := by
        rw [←padicValNat.pow, ←factorization_def _ hp, ← factorization_def _ hp]
        refine (Nat.factorization_prime_le_iff_dvd ?_ ?_).mpr h3 p hp
        repeat positivity
      let xp := min (min (padicValNat p a) (padicValNat p b)) (padicValNat p c)

      -- the padic value of sum of three natural number a b c is greater than min of each of their padic value
      have hle_aux : xp ≤ padicValNat p (a + b + c) := by 
        have aux1 : min (padicValNat p (a + b)) (padicValNat p c) ≤ padicValNat p (a + b + c) := by 
          have aux : (a : ℚ) + b + c ≠ 0 := by 
            norm_cast
            positivity
          obtain aux2 := @padicValRat.min_le_padicValRat_add p hp1 (a + b) c aux 
          norm_cast at aux2
        
        -- `min (padicValNat p a ) (padicValNat p b) ≤ padicValNat p (a + b)`, the padic value of sum of two natural number a b is greater than min of each of their padic value
        have aux2 : min (padicValNat p a ) (padicValNat p b) ≤ padicValNat p (a + b) := by
          have aux : (a : ℚ) + b ≠ 0 := by
            norm_cast
            positivity
          obtain aux2 := @padicValRat.min_le_padicValRat_add p hp1 a b aux
          norm_cast at aux2
        have aux3 : xp ≤ min (padicValNat p (a + b)) (padicValNat p c) := by 
          exact inf_le_inf_right (padicValNat p c) aux2
        linarith
      -- xp is equal to one of `padicValNat p a`, `padicValNat p b` and `padicValNat p c`, since the definition of xp is minimal of these number.
      have xpeq_or : xp = padicValNat p a ∨ xp = padicValNat p b ∨ xp = padicValNat p c := by 
        omega
      obtain xpeq1 | xpeq1 | xpeq1 := xpeq_or
      · -- the case xp = padicValNat p a
        have aux : padicValNat p a + padicValNat p b + padicValNat p c ≤ 
          (k ^ 2 + k + 1) * (padicValNat p a) := by 
          have aux1 : padicValNat p b ≤ k ^ 2 * padicValNat p a := by 
            calc 
              _ ≤ k * padicValNat p c := by 
                exact hle2
              _ ≤ k * (k * padicValNat p a) := by 
                apply mul_le_mul
                simp
                exact hle3
                exact Nat.zero_le (padicValNat p c)
                linarith
              _ = _ := by ring
          linarith
        rw [xpeq1] at hle_aux
        nlinarith
      · -- the case xp = padicValNat p b
        have aux : padicValNat p a + padicValNat p b + padicValNat p c ≤ 
          (k ^ 2 + k + 1) * (padicValNat p b) := by 
          have aux1 : padicValNat p c ≤ k ^ 2 * padicValNat p b := by 
            calc 
              _ ≤ k * padicValNat p a := by 
                exact hle3
              _ ≤ k * (k * padicValNat p b) := by 
                apply mul_le_mul
                simp
                exact hle1
                exact Nat.zero_le (padicValNat p a)
                linarith
              _ = _ := by ring
          linarith
        rw [xpeq1] at hle_aux
        nlinarith
      · -- the case xp = padicValNat p c
        have aux : padicValNat p a + padicValNat p b + padicValNat p c ≤ 
          (k ^ 2 + k + 1) * (padicValNat p c) := by 
          have aux1 : padicValNat p a ≤ k ^ 2 * padicValNat p c := by 
            calc 
              _ ≤ k * padicValNat p b := by 
                exact hle1
              _ ≤ k * (k * padicValNat p c) := by 
                apply mul_le_mul
                simp
                exact hle2
                exact Nat.zero_le (padicValNat p b)
                linarith
              _ = _ := by ring
          linarith
        rw [xpeq1] at hle_aux
        nlinarith
    -- use positivity to prove the remaining goal. 
    repeat positivity
