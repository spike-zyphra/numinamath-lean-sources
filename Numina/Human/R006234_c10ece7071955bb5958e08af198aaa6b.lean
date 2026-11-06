import Mathlib

open Nat

theorem number_theory_635041 (k : ℕ) (N N': ℕ) (hN : (Nat.digits 10 N).length = k) (kge : k ≥ 1)
  (m : ℕ) (hm : m > 0) (hdiv : m ∣ N ∧ m ∣ 10 ^ k - 1)  
  (hN' : N' = Nat.ofDigits 10 ([(Nat.digits 10 N).getLastI] ++ (Nat.digits 10 N).reverse.tail.reverse)):
  m ∣ N' := by 
  obtain ⟨hdiv1, hdiv2⟩ := hdiv
  -- mainly use the following theorem
  -- Nat.ofDigits_div_eq_ofDigits_tail
  -- Nat.ofDigits_append
  have h1 : N' = 10 * N - ((Nat.digits 10 N).getLastI : ℕ) * (10 ^ k - 1) := by 
    rw [hN', Nat.ofDigits_append]
    have aux1 : [(digits 10 N).getLastI].length = 1 := by 
      exact rfl
    rw [aux1]
    simp
    have aux2 : 10 * N = 10 * (ofDigits 10 (Nat.digits 10 N)) := by 
      simp
      exact Eq.symm (ofDigits_digits 10 N)
    -- Nat.digits is not empty iff N is not zero
    have neq : Nat.digits 10 N ≠ [] := by 
      rw [←hN] at kge
      exact List.ne_nil_of_length_pos kge

    have aux3 : (Nat.digits 10 N) = (Nat.digits 10 N).dropLast ++ [(digits 10 N).getLastI] := by 
      have aux4 : (digits 10 N).getLastI = (digits 10 N).getLast neq := by 
        rw [List.getLastI_eq_getLast?]
        refine Option.iget_of_mem ?_
        simp
        exact List.getLast?_eq_getLast (digits 10 N) neq
      rw [aux4]
      exact Eq.symm (List.dropLast_concat_getLast neq)
    rw [aux3] at aux2
    rw [aux2, Nat.ofDigits_append]
    have len_aux1 : (digits 10 N).dropLast.length = k - 1 := by 
      rw [←hN]
      simp
    rw [len_aux1]
    simp
    rw [mul_add]
    
    have aux4 : 10 * (10 ^ (k - 1) * (digits 10 N).getLastI) = 
      10 ^ k *  (digits 10 N).getLastI := by 
      have aux5 : 10 ^ k = 10 ^ (k - 1) * 10 := by 
        nth_rw 1 [show k = k - 1 + 1 by omega]
        rw [pow_add]
        simp
      rw [aux5]
      ring
    rw [aux4]
    have ge_aux : 10 ^ k ≥  1 := by 
      exact one_le_pow' k 9
    have aux5 : (digits 10 N).getLastI + 10 * ofDigits 10 (digits 10 N).dropLast 
      + (digits 10 N).getLastI * (10 ^ k - 1) =
      10 * ofDigits 10 (digits 10 N).dropLast + 10 ^ k * (digits 10 N).getLastI := by 
      zify
      rw [Nat.cast_sub]
      norm_num
      ring
      exact ge_aux
    omega
  rw [h1]
  have mdvd : m ∣ 10 * N := by 
    exact Dvd.dvd.mul_left hdiv1 10
  have dvd2 : m ∣ (digits 10 N).getLastI * (10 ^ k - 1) := by 
    exact Dvd.dvd.mul_left hdiv2 (digits 10 N).getLastI
  exact dvd_sub' mdvd dvd2