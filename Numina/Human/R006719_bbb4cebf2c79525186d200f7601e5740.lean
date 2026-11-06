import Mathlib

open Finset

theorem number_theory_640512 {k : ℕ} (a : ℕ → ℕ)
  (ha : ∀ i ∈ Icc 0 k, a i = 0 ∨ a i = 1)
  (h : ¬(k + 1 ≡ 0 [MOD 4])) :
  ¬ 5 ∣ ∑ i ∈ Icc 0 k, Nat.factorial (a i) * 2 ^ i := by 
  have h1 :∀ n, n ∈ Icc 0 k →  ∑ i ∈ Icc 0 n, Nat.factorial (a i) * 2 ^ i = 2 ^ (n + 1) - 1 := by 
    intro n 
    induction n with 
    | zero => 
      simp
      have aeq : a 0 = 0 ∨ a 0 = 1 := by
        apply ha
        simp
      omega
    | succ m ih => 
      intro h1
      have seteq1 : Icc 0 (m + 1) = insert (m + 1) (Icc 0 m) := by 
        refine Eq.symm (Nat.Icc_insert_succ_right ?_)
        linarith
      rw [seteq1, sum_insert, ih]
      have eq1 : (a (m + 1)).factorial = 1 := by 
        have aeq : a (m + 1) = 0 ∨ a (m + 1) = 1 := by
          apply ha
          simp
          simp at h1
          exact h1
        obtain aeq | aeq := aeq
        simp [aeq]
        simp [aeq]
      rw [eq1]
      simp
      zify
      repeat rw [Nat.cast_sub]
      norm_num
      ring
      exact Nat.one_le_two_pow
      exact Nat.one_le_two_pow
      simp 
      simp at h1
      omega
      simp
  rw [h1]
  -- discuss by cases the residue of (k + 1) modulo 4
  have modeq : (k + 1) % 4 = 0 ∨ (k + 1) % 4 = 1 ∨ (k + 1) % 4 = 2 ∨ (k + 1) % 4 = 3 := by 
    omega
  obtain modeq0 | modeq1 | modeq2 | modeq3 := modeq
  · -- the case (k + 1) % 4 = 0
    have aux : k + 1 ≡ 0 [MOD 4] := by
      exact modeq0
    contradiction
  · -- the case (k + 1) % 4 = 1
    have aux : ∃ m, k + 1 = 4 * m + 1 := by 
      use ((k + 1) / 4)
      omega
    obtain ⟨m, hm⟩ := aux
    zify
    rw [hm, Nat.cast_sub]
    by_contra hc
    norm_num at hc
    have aux2 : 2 ^ (4 * m + 1) ≡ 1 [ZMOD 5] := by 
      exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) hc)
    rw [pow_add, pow_mul] at aux2
    simp at aux2
    have aux3 : 16 ^ m * 2 ≡ 2 [ZMOD 5] := by 
      calc 
        _ ≡ 1 ^ m * 2 [ZMOD 5] := by 
          have mod_aux : 16 ≡ 1 [ZMOD 5] := by
            exact rfl
          refine Int.ModEq.mul ?_ rfl
          exact Int.ModEq.pow m mod_aux
        _ ≡ _ [ZMOD 5] := by
          simp
    have aux4 : 1 ≡ 2 [ZMOD 5] := by
      calc 
        _ ≡ 16 ^ m * 2 [ZMOD 5] := by
          exact id (Int.ModEq.symm aux2)
        _ ≡ 2 [ZMOD 5] := by 
          exact aux3
    obtain aux5 := Int.ModEq.dvd aux4
    norm_num at aux5
    exact Nat.one_le_two_pow
  · -- the case (k + 1) % 4 = 2
    have aux : ∃ m, k + 1 = 4 * m + 2 := by 
      use ((k + 1) / 4)
      omega
    obtain ⟨m, hm⟩ := aux
    zify
    rw [hm, Nat.cast_sub]
    by_contra hc
    norm_num at hc
    have aux2 : 2 ^ (4 * m + 2) ≡ 1 [ZMOD 5] := by 
      exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) hc)
    rw [pow_add, pow_mul] at aux2
    simp at aux2
    have aux3 : 16 ^ m * 4 ≡ 4 [ZMOD 5] := by 
      calc 
        _ ≡ 1 ^ m * 4 [ZMOD 5] := by 
          have mod_aux : 16 ≡ 1 [ZMOD 5] := by
            exact rfl
          refine Int.ModEq.mul ?_ rfl
          exact Int.ModEq.pow m mod_aux
        _ ≡ _ [ZMOD 5] := by
          simp
    have aux4 : 1 ≡ 4 [ZMOD 5] := by
      calc 
        _ ≡ 16 ^ m * 4 [ZMOD 5] := by
          exact id (Int.ModEq.symm aux2)
        _ ≡ 4 [ZMOD 5] := by 
          exact aux3
    obtain aux5 := Int.ModEq.dvd aux4
    norm_num at aux5
    exact Nat.one_le_two_pow
  · -- the case (k + 1) % 4 = 3
    have aux : ∃ m, k + 1 = 4 * m + 3 := by 
      use ((k + 1) / 4)
      omega
    obtain ⟨m, hm⟩ := aux
    zify
    rw [hm, Nat.cast_sub]
    by_contra hc
    norm_num at hc
    have aux2 : 2 ^ (4 * m + 3) ≡ 1 [ZMOD 5] := by 
      exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) hc)
    rw [pow_add, pow_mul] at aux2
    simp at aux2
    have aux3 : 16 ^ m * 8 ≡ 3 [ZMOD 5] := by 
      calc 
        _ ≡ 1 ^ m * 3 [ZMOD 5] := by 
          have mod_aux : 16 ≡ 1 [ZMOD 5] := by
            exact rfl
          refine Int.ModEq.mul ?_ rfl
          exact Int.ModEq.pow m mod_aux
        _ ≡ _ [ZMOD 5] := by
          simp
    have aux4 : 1 ≡ 3 [ZMOD 5] := by
      calc 
        _ ≡ 16 ^ m * 8 [ZMOD 5] := by
          exact id (Int.ModEq.symm aux2)
        _ ≡ 3 [ZMOD 5] := by 
          exact aux3
    obtain aux5 := Int.ModEq.dvd aux4
    norm_num at aux5
    exact Nat.one_le_two_pow
  simp