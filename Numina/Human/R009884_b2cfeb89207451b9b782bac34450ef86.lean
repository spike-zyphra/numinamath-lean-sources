import Mathlib

/- How many distinct four-digit numbers are divisible by 3 and have 23 as their last two digits? -/
theorem number_theory_12257 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23} = 30 := by
  -- We observe that 3 ∣ n ∧ n % 100 = 23 is equivalent to n ≡ 123 [MOD 300].
  have lm (n : ℕ) : (3 ∣ n ∧ n % 100 = 23) ↔ (n ≡ 123 [MOD 300]) := by
    -- Break the iff into two implications.
    apply Iff.intro <;> intro h
    . have hco : Nat.Coprime 3 100 := by
        norm_num
      have h₀ : n ≡ Nat.chineseRemainder hco 0 23 [MOD 3 * 100] := by
        apply Nat.chineseRemainder_modEq_unique
        apply Dvd.dvd.modEq_zero_nat
        tauto
        rw [Nat.ModEq.eq_1]
        norm_num
        tauto
      have h₁ : 123 ≡ Nat.chineseRemainder hco 0 23 [MOD 3 * 100] := by
        apply Nat.chineseRemainder_modEq_unique
        apply Dvd.dvd.modEq_zero_nat
        norm_num
        rw [Nat.ModEq.eq_1]
      exact Nat.ModEq.trans h₀ h₁.symm
    . refine ⟨?_, ?_⟩ <;> rw [show 300 = 3 * 100 by norm_num] at h
      . apply Nat.ModEq.of_mul_right at h
        rw [Nat.ModEq.eq_1] at h
        norm_num at h
        exact Nat.dvd_of_mod_eq_zero h
      . apply Nat.ModEq.of_mul_left at h
        rw [Nat.ModEq.eq_1] at h
        norm_num at h
        exact h
  -- Create a bijection between two sets (let's call them A and B respectively for our hypothesis naming).
  let φ : {n : ℕ | 3 ≤ n ∧ n ≤ 32} → {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23} := fun n ↦ ⟨300 * n + 123, ?_⟩
  pick_goal 2
  -- Show that 300 * n + 123 belongs to the set on the right if n belongs to the set on the left, so that φ is a function.
  obtain ⟨n, h⟩ := n
  simp at h ⊢
  omega
  -- Now show that the two sets have the same encard because φ is a bijection.
  have ABeq_encard : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23}.encard = {n : ℕ | 3 ≤ n ∧ n ≤ 32}.encard := by
    refine (Set.encard_congr (Equiv.ofBijective φ ⟨fun m n φeq ↦ ?_, fun ⟨n, h₀, h₁⟩ ↦ ?_⟩)).symm -- Note this ".symm".
    . -- Show that φ is injective.
      obtain ⟨m, _, _⟩ := m
      obtain ⟨n, _, _⟩ := n
      simp [φ] at φeq
      congr
    . -- Show that φ is surjective.
      simp [φ]
      simp at h₀
      rw [lm] at h₁
      rw [<-@Nat.sub_add_cancel n 123] at h₁
      pick_goal 2
      omega -- Use omega to show that n ≥ 123.
      nth_rewrite 3 [<-Nat.zero_add 123] at h₁
      apply Nat.ModEq.add_right_cancel' at h₁
      rw [Nat.modEq_zero_iff_dvd, dvd_iff_exists_eq_mul_left] at h₁
      obtain ⟨k, h₁⟩ := h₁
      replace h₁ : n = 300 * k + 123 := by
        calc
          n = n - 123 + 123 := by rw [Nat.sub_add_cancel]; omega -- Use omega to show that n ≥ 123.
          _ = 300 * k + 123 := by rw [Nat.mul_comm, h₁]
      simp [h₁]
      omega
  have B_ncard : {n : ℕ | 3 ≤ n ∧ n ≤ 32}.ncard = 30 := by
    calc
      {n : ℕ | 3 ≤ n ∧ n ≤ 32}.ncard = (Set.Icc 3 32).ncard := by congr
      _ = (Finset.Icc 3 32).card := by rw [<-Finset.coe_Icc, Set.ncard_coe_Finset] -- Set.ncard cast to Finset.card.
      _ = 30 := by apply Nat.card_Icc
  have B_encard : {n : ℕ | 3 ≤ n ∧ n ≤ 32}.encard = 30 := by
    rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, B_ncard] -- Set.ncard = Set.encard.toNat.
    norm_cast
    apply Set.finite_of_ncard_pos -- Show that the set B is finite.
    simp [B_ncard]
  have A_encard : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23}.encard = 30 := by
    exact Eq.trans ABeq_encard B_encard
  have A_ncard : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23}.ncard = 30 := by
    rw [Set.Finite.encard_eq_coe, <-Set.ncard_def] at A_encard
    norm_cast at A_encard
    apply Set.finite_of_encard_eq_coe A_encard
  exact A_ncard
