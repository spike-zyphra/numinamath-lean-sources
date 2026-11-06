import Mathlib

def E (k : ℕ) := 33 * k + 9

theorem number_theory_635805 (k : ℕ) : (9 ^ E k + 2022) % 299 = 138 := by 
  have h1 : 299 = 13 * 23 := by norm_num 
  -- We start by expressing 299 as a product of primes, which is $13 \times 23$.
  have hcop : Nat.Coprime 13 23 := by norm_num
  -- Next, we verify that 13 and 23 are coprime.
  have modeq1 : 9^E k ≡ 1 [ZMOD 13] := by
    unfold E
    have aux1 : 9 ^ 3 ≡ 1 [ZMOD 13] := by rfl
    have aux2 : (9 : ℤ) ^ (33 * k + 9) = (9 ^ 3) ^ (11 * k + 3) := by 
      rw [←pow_mul]
      ring
    rw [aux2]
    obtain aux3 :=  Int.ModEq.pow (11 * k + 3) aux1
    simp at aux3
    simp [aux3]
  have modeq2 : 9^E k ≡ 2 [ZMOD 23] := by
    unfold E
    have aux1 : 9 ^ 11 ≡ 1 [ZMOD 23] := by rfl
    rw [pow_add]
    have aux2 : 9 ^ (33 * k) ≡ 1 [ZMOD 23] := by 
      have aux3 : (9 : ℤ) ^ (33 * k) = (9 ^ 11) ^ (3 * k) := by 
        rw [← pow_mul]
        ring
      rw [aux3]
      obtain aux4 := Int.ModEq.pow (3 * k) aux1
      conv at aux4 => 
        rhs
        simp
      exact aux4
    calc 
      _ ≡ 1 * 9 ^ 9 [ZMOD 23] := by 
        exact Int.ModEq.mul aux2 rfl
      _ ≡ 2 [ZMOD 23] := by 
        rfl
  have modeq3 : 2022 ≡ 7 [ZMOD 13] := by rfl
  have modeq4 : 2022 ≡ 21 [ZMOD 23] := by rfl
  have mod1 : 9 ^ E k + 2022 ≡ 8 [ZMOD 13] := by 
    obtain aux := Int.ModEq.add modeq1 modeq3
    simp at aux
    exact aux
  have mod2 : 9 ^ E k + 2022 ≡ 0 [ZMOD 23] := by 
    obtain aux := Int.ModEq.add modeq2 modeq4
    simp at aux
    exact aux
  have dvd1 : (23 : ℤ) ∣ 9 ^ E k + 2022 := by 
    exact Int.dvd_of_emod_eq_zero mod2
  obtain ⟨m, hm⟩ := dvd1
  have mod3 : 23 * m ≡ 8 [ZMOD 13] := by 
    rw [hm] at mod1
    exact mod1
  have mod4 : m ≡ 6 [ZMOD 13] := by  
    have aux : 5 * m ≡ 4 [ZMOD 13] := by 
      apply Int.modEq_of_dvd
      obtain aux1 := Int.ModEq.dvd mod3
      have aux' : 13 ∣ 8 - 10 * m := by 
        omega
      have aux2 : (8 : ℤ) - 10 * m = 2 * (4 - 5 * m) := by 
        ring
      rw [aux2] at aux'
      have cop2 : Nat.Coprime 13 2 := by 
        norm_num
      exact Int.dvd_of_dvd_mul_right_of_gcd_one aux' hcop
    have aux3 : (5 * m) * 8 ≡ 4 * 8 [ZMOD 13] := by 
      exact Int.ModEq.mul aux rfl
    have aux4 : 5 * m * 8 = 40 * m := by ring
    rw [aux4] at aux3
    have aux5 : 1 * m ≡ 6 [ZMOD 13] := by 
      calc 
        _ ≡ 40 * m [ZMOD 13]:=  by 
          refine Int.ModEq.mul rfl rfl
        _ ≡ 4 * 8 [ZMOD 13] := by exact aux3
        _ ≡ 6 [ZMOD 13]:= by 
          rfl
    simp at aux5
    exact aux5
  have dvd2 : 13 ∣ m - 6 := by 
    exact Int.dvd_sub_of_emod_eq mod4
  obtain ⟨t, ht⟩ := dvd2
  have meq : m = 13 * t + 6 := by
    linarith
  rw [meq] at hm
  zify
  rw [hm]
  omega