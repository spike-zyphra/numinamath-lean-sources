import Mathlib

/- The number N is a two-digit number.

    When N is divided by 9, the remainder is 1.
    When N is divided by 10, the remainder is 3. What is the 
    remainder when N is divided by 11?

(A) 0(B) 2(C) 4(D) 5(E) 7-/
theorem number_theory_92964 {N : ℕ} (hN : N ∈ Finset.Icc 10 99) (h1 : N ≡ 1 [MOD 9]) (h2 : N ≡ 3 [MOD 10]) :
N % 11 = 7 := by {
  norm_num [Finset.mem_Icc] at hN

  -- We could just do a case distinction by hand, but to be more principled,
  -- we use the Chinese Remainder Theorem to deduce that N ≡ 73 [MOD 90].
  -- The claim then follows because N has two digits.

  suffices : N = 73
  rw [this]


  -- Now it suffices to show that N = 73. We essentially apply Chinese
  -- Remainder Theorem here, already specifiying the answer to make
  -- it easier.
  have h910 : Nat.Coprime 9 10 := by norm_num
  have h1a2 : N ≡ 73 [MOD 9] ∧ N ≡ 73 [MOD 10] := ⟨h1,h2⟩
  have h90 := (Nat.modEq_and_modEq_iff_modEq_mul h910).1 h1a2

  -- From here on it is just simple inequalities to deduce the claim,
  -- since 73 is the only number between 10 and 99 that is ≡ 73 [MOD 90].
  simp at h90
  unfold Nat.ModEq at h90
  simp at h90
  rw [Nat.mod_def] at h90
  -- We show that N / 90 ≤ 1 , then do a case distinction according
  -- to whether it is 0 or 1, which quickly lets us exlude 1.
  have : N / 90 ≤ 1 := by {
    rcases hN with ⟨hN1,hN2⟩
    rw [Nat.div_le_iff_le_mul_add_pred]
    simp
    linarith
    trivial
  }
  rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
  rcases this with hN901 | hN900 
  rw [hN901] at h90
  exact h90

  rw [hN900] at h90
  exfalso
  apply Nat.eq_add_of_sub_eq at h90
  simp at h90
  rw [h90] at hN
  trivial
  rw [mul_comm]
  apply Nat.mul_le_of_le_div
  rw [hN900]
}