import Mathlib

lemma l₁ {n} : 1 < n ∧ n < 10 → ¬n ≡ 1 [MOD 9] := by
  rintro ⟨ n_gt, n_lt ⟩ n_congr
  interval_cases n
  all_goals
    contrapose! n_congr
    decide

theorem number_theory_245520 (a b : ℕ)
  (a_in : a ∈ Finset.Ico (10^6) (10^7))
  (b_in : b ∈ Finset.Ico (10^6) (10^7))
  (a_ne_b : a ≠ b)
  (digits_a : (Nat.digits 10 a).Perm (List.range' 1 7))
  (digits_b : (Nat.digits 10 b).Perm (List.range' 1 7))
  : ¬ b ∣ a := by
  have sum_a : (Nat.digits 10 a).sum = 28 := by
    have := List.Perm.sum_eq digits_a
    aesop

  have sum_b : (Nat.digits 10 b).sum = 28 := by
    have := List.Perm.sum_eq digits_b
    aesop

  rintro ⟨ n, n_eq ⟩
  have mod_sum_a := Nat.modEq_nine_digits_sum a
  have mod_sum_b := Nat.modEq_nine_digits_sum b
  rw [sum_a] at mod_sum_a
  rw [sum_b] at mod_sum_b
  replace mod_sum_a : a ≡ 1 [MOD 9] := mod_sum_a
  replace mod_sum_b : b ≡ 1 [MOD 9] := mod_sum_b
  subst n_eq
  obtain ⟨ bn_ge, bn_lt ⟩ := by simpa using a_in
  obtain ⟨ b_ge, b_lt ⟩ := by simpa using b_in
  have pos_n : 0 < n := by
    suffices n ≠ 0 from Nat.zero_lt_of_ne_zero this
    intro ne
    subst ne
    omega
  have : n ≠ 1 := by
    intro ne
    subst ne
    simp at a_ne_b
  replace : 1 < n := by omega

  have n_lt_10 : n < 10 := by
    by_contra! n_ge
    have : b * n < 10 * 1000000 := by
      linarith

    have : 1000000 * 10 ≤ b * n := by
      exact Nat.mul_le_mul b_ge n_ge
    linarith

  obtain ⟨ k, k_mod_eq ⟩ : ∃ k, n ≡ k [MOD 9] :=
    Exists.intro n rfl

  have : b * n ≡ 1 * k [MOD 9] :=
    Nat.ModEq.mul mod_sum_b k_mod_eq
  simp at this

  have : k ≡ 1 [MOD 9] := by
    exact Nat.ModEq.trans (id (Nat.ModEq.symm this)) mod_sum_a

  have : n ≡ 1 [MOD 9] := by
    exact Nat.ModEq.trans k_mod_eq this

  exact @l₁ n ⟨ by assumption, n_lt_10 ⟩ this
