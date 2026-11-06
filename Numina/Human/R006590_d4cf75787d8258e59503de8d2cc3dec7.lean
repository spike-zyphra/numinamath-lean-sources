import Mathlib

open Nat


lemma nat_le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega

lemma nat_div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [nat_le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega

lemma nat_div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, nat_div_le_iff_le_mul h]

theorem number_theory_638923 (N : ℕ) (hN : Even N) (hN1 : N ≥ 4) :
  (Nat.digits 10 (5^N))[2]! + (Nat.digits 10 (5^N))[1]! + (Nat.digits 10 (5^N))[0]! = 13 := by 
  have digits_aux (n : ℕ) (npos : n > 0): (Nat.digits 10 n)[1]! = 
    (Nat.digits 10 (n/ 10))[0]! := by 
    rw [Nat.digits_of_two_le_of_pos]
    simp
    linarith
    exact npos
  have digits_aux2 (n : ℕ) (npos : n > 0): (Nat.digits 10 n)[0]! = n % 10 := by 
    rw [Nat.digits_of_two_le_of_pos]
    simp
    linarith
    linarith
  have h1 : (Nat.digits 10 (5^N))[0]! = (5 ^ N) % 10 := by 
    simp
  have h2 : (Nat.digits 10 (5^N))[1]! = (Nat.digits 10 (5^N / 10))[0]! := by 
    simp
  have h3 : (Nat.digits 10 (5^N))[2]! = (Nat.digits 10 (5^N / 10))[1]! := by
    simp only [Nat.reduceLeDiff, Nat.ofNat_pos, pow_pos, Nat.digits_of_two_le_of_pos,
      List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ, Nat.default_eq_zero]
  have h4 : (Nat.digits 10 (5^N))[2]! = (Nat.digits 10 (5^N / 100))[0]! := by 
    rw [h3]
    have pos : (5 ^ N / 10) > 0 := by 
      refine Nat.div_pos ?_ ?_
      · have pow_ge : 5 ^ N ≥ 5 ^ 4 := by 
          apply Nat.pow_le_pow_right
          linarith
          linarith
        linarith
      · norm_num
    obtain aux := digits_aux (5 ^ N / 10) pos
    rw [aux]
    have eq1 : (5 ^ N / 10 / 10) = 5 ^ N / 100 := by
      refine (nat_div_eq_iff ?_).mpr ?_ 
      · linarith
      · constructor
        · omega
        · omega
    rw [eq1]
  -- by induction, we can prove that forall k : ℕ, k ≥ 2, then 5 ^ (k + k) ≡ 625 [ZMOD 1000]
  have modeq0 (k : ℕ) (kge : k ≥ 2) : 5 ^ (k + k) ≡ 625 [ZMOD 1000] := by 
    have kge : k ≥ 2 := by 
      linarith
    induction' kge with n ih1 ih2
    · rfl
    · simp at ih1
      obtain ih2' := ih2 ih1
      calc 
        _ ≡ 5 ^ (n + n) * 25 [ZMOD 1000] := by
          congr
          simp
          ring
        _ ≡ 625 * 25 [ZMOD 1000] := by 
          exact Int.ModEq.mul (ih2 ih1) rfl
  obtain ⟨k, hk⟩ := hN
  -- use the induction result in the modeq0, we can deduce the following result, and use this result we can get the last three digits in the digits representation of 5 ^ N is "625".
  have modeq : 5 ^ N ≡ 625 [ZMOD 1000] := by 
    have kge : k ≥ 2 := by
      linarith
    rw [hk]
    exact modeq0 k kge
  obtain ⟨m, hm⟩ := Int.ModEq.dvd (Int.ModEq.symm modeq)
  have pow_ge : 5 ^ N ≥ 5 ^ 4 := by 
    apply Nat.pow_le_pow_right
    linarith
    linarith
  have eq1 : 5 ^ N = m * 1000 + 625 := by
    linarith
  have aux1 : (digits 10 (5 ^ N))[0]! = 5 := by 
    rw [h1]
    zify
    rw [eq1]
    omega
  have aux2 : (digits 10 (5 ^ N))[1]! = 2 := by
    rw [h2, digits_aux2]
    zify
    rw [eq1]
    omega
    refine Nat.div_pos ?_ ?_
    · linarith
    · linarith
  have aux3 : (digits 10 (5 ^ N))[2]! = 6 := by
    rw [h4, digits_aux2]
    zify
    rw [eq1]
    omega
    refine Nat.div_pos ?_ ?_
    · linarith
    · linarith
  rw [aux1, aux2, aux3]