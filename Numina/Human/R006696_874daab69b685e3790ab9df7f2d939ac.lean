import Mathlib

theorem number_theory_640262 (k : ℕ) (hk : k > 0) (N : ℕ) (hN : N = 7^(7^k)) :
  (Even k →  N % 10 = 7 ∧ N % 100 = 7 ) ∧ (Odd k → N % 10 = 3 ∧ N % 100 = 43) := by 
  constructor
  · -- the case Even k
    intro h
    zify
    have mod1 : 7 ^ 4 ≡ 1 [ZMOD 10] := by 
      rfl
    have mod2 : 7 ^ k ≡ 1 [ZMOD 4] := by 
      have aux : 7 ≡ - 1 [ZMOD 4] := by 
        rfl
      calc 
        _ ≡ (-1) ^ k [ZMOD 4] := by 
          exact Int.ModEq.pow k aux
        _ ≡ 1 [ZMOD 4] := by 
          congr
          exact Even.neg_one_pow h
    have mod3 : 7 ^ 4 ≡ 1 [ZMOD 100] := by 
      rfl
    obtain aux1 := Int.ModEq.dvd (Int.ModEq.symm mod2)
    obtain ⟨t, ht⟩ := aux1
    have aux2 : 7 ^ k = 4 * t + 1 := by 
      linarith
    have tge0 : t ≥ 0:= by 
      have auxge : (7 : ℤ) ^ k ≥ 1 := by 
        refine one_le_pow₀ ?_
        norm_num
      linarith
    have seqt : ∃ (s : ℕ), s = t := by 
      use (t.toNat)
      omega
    obtain ⟨s, hs⟩ := seqt
    rw [←hs] at aux2
    norm_cast at aux2
    constructor
    · 
      rw [hN, aux2, pow_add]
      have modaux : (7 ^ (4 * s) * 7 ^ 1 : ℕ) ≡ 7 [ZMOD 10] := by
        calc 
          _ ≡ 1 * 7 ^ 1 [ZMOD 10] := by
            norm_num
            have aux3 : 7 ^ (4 * s) ≡ 1 [ZMOD 10] := by
              rw [pow_mul]
              calc
                _ ≡ 1 ^ s [ZMOD 10] := by 
                  exact Int.ModEq.pow s mod1
                _ ≡ 1 [ZMOD 10] := by 
                  simp
            conv => 
              rhs
              rw [show (7 : ℤ) = 1 * 7 by norm_num]
            exact Int.ModEq.mul aux3 rfl
          _ ≡ 7 [ZMOD 10] := by
            norm_num
      exact modaux
    · 
      rw [hN, aux2, pow_add]
      have modaux : (7 ^ (4 * s) * 7 ^ 1 : ℕ) ≡ 7 [ZMOD 100] := by
        calc 
          _ ≡ 1 * 7 ^ 1 [ZMOD 100] := by
            norm_num
            have aux3 : 7 ^ (4 * s) ≡ 1 [ZMOD 100] := by
              rw [pow_mul]
              calc
                _ ≡ 1 ^ s [ZMOD 100] := by 
                  exact Int.ModEq.pow s mod1
                _ ≡ 1 [ZMOD 100] := by 
                  simp
            conv => 
              rhs
              rw [show (7 : ℤ) = 1 * 7 by norm_num]
            exact Int.ModEq.mul aux3 rfl
          _ ≡ 7 [ZMOD 100] := by
            norm_num
      exact modaux
    
  · -- the case Odd k
    intro h
    zify
    have mod1 : 7 ^ 4 ≡ 1 [ZMOD 10] := by 
      rfl
    have mod2 : 7 ^ k ≡ 3 [ZMOD 4] := by 
      have aux : 7 ≡ - 1 [ZMOD 4] := by 
        rfl
      calc 
        _ ≡ (-1) ^ k [ZMOD 4] := by 
          exact Int.ModEq.pow k aux
        _ ≡ -1 [ZMOD 4] := by 
          congr
          exact Odd.neg_one_pow h
    have mod3 : 7 ^ 4 ≡ 1 [ZMOD 100] := by 
      rfl
    obtain aux1 := Int.ModEq.dvd (Int.ModEq.symm mod2)
    obtain ⟨t, ht⟩ := aux1
    have aux2 : 7 ^ k = 4 * t + 3 := by 
      linarith
    have tge0 : t ≥ 0:= by 
      have auxge : (7 : ℤ) ^ k ≥ 1 := by 
        refine one_le_pow₀ ?_
        norm_num
      linarith
    have seqt : ∃ (s : ℕ), s = t := by 
      use (t.toNat)
      omega
    obtain ⟨s, hs⟩ := seqt
    rw [←hs] at aux2
    norm_cast at aux2
    constructor
    · 
      rw [hN, aux2, pow_add]
      have modaux : (7 ^ (4 * s) * 7 ^ 3 : ℕ) ≡ 3 [ZMOD 10] := by
        calc 
          _ ≡ 1 * 7 ^ 3 [ZMOD 10] := by
            norm_num
            have aux3 : 7 ^ (4 * s) ≡ 1 [ZMOD 10] := by
              rw [pow_mul]
              calc
                _ ≡ 1 ^ s [ZMOD 10] := by 
                  exact Int.ModEq.pow s mod1
                _ ≡ 1 [ZMOD 10] := by 
                  simp
            exact Int.ModEq.mul aux3 rfl
          _ ≡ 7 ^ 3 [ZMOD 10] := by
            norm_num
          _ ≡ 3 [ZMOD 10] := by
            rfl
      exact modaux
    · 
      rw [hN, aux2, pow_add]
      have modaux : (7 ^ (4 * s) * 7 ^ 3 : ℕ) ≡ 43 [ZMOD 100] := by
        calc 
          _ ≡ 1 * 7 ^ 3 [ZMOD 100] := by
            norm_num
            have aux3 : 7 ^ (4 * s) ≡ 1 [ZMOD 100] := by
              rw [pow_mul]
              calc
                _ ≡ 1 ^ s [ZMOD 100] := by 
                  exact Int.ModEq.pow s mod1
                _ ≡ 1 [ZMOD 100] := by 
                  simp
            exact Int.ModEq.mul aux3 rfl
          _ ≡ 43 [ZMOD 100] := by
            rfl
      exact modaux
    