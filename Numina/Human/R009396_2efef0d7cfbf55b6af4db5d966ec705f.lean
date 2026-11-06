import Mathlib

/-In writing the integers from 10 through 99 inclusive, how many times is the digit 6 written?-/
theorem algebra_15469 : ∑n ∈ (Finset.Icc 10 99), (Nat.digits 10 n).count 6 = 19 := by
  -- The 9 integers 16, 26, $\ldots$, 86 and 96 each have 6 as a units digit.  The 10 integers 60, 61, $\ldots$, 68 and 69 each have 6 as a tens digit.  In total, there are $10+9=\boxed{19}$ appearances of the digit 6.
  -- Note: This question asks for the number of times the digit 6 is written, not the number of numbers with the digit 6.
  -- firstly, we prove that, when n ≤ 99, 6 ∈ (Nat.digits 10 n) equals to (n % 10 = 6 ∨ (n / 10) % 10 = 6)
  have eq_iff : ∀n ≤ 99, 6 ∈ (Nat.digits 10 n) ↔ (n % 10 = 6 ∨ (n / 10) % 10 = 6) := by
    intro n hn
    constructor
    . intro hn'
      by_cases h_ne_zero: n = 0
      . rw [h_ne_zero] at hn'
        absurd hn'
        rw [Nat.digits_zero]
        simp
      by_cases h: n < 10
      . rw [Nat.digits_of_lt 10 n h_ne_zero h] at hn'
        simp at hn'
        rw [hn'.symm]
        omega
      simp at h
      rw [(Nat.head!_digits (by norm_num)).symm]
      obtain ⟨l, hl⟩ := (by simp: ∃l, l = Nat.digits 10 n)
      have length_of_l : l.length = 2 := by
        rw [hl, Nat.digits_len]
        simp
        apply Nat.log_eq_one_iff.mpr
        repeat omega
      obtain ⟨ones, tens, h⟩ := List.length_eq_two.mp length_of_l
      rw [hl.symm, h] at hn'
      rw [hl.symm, h]
      simp at hn'
      obtain (hn' | hn') := hn'
      . -- 6 = ones
        simp
        apply Or.inl
        exact hn'.symm
      . -- 6 = tens
        apply Or.inr
        have : n = Nat.ofDigits 10 l := by
          rw [hl]
          exact Eq.symm (Nat.ofDigits_digits 10 n)
        rw [this, h]
        have : Nat.ofDigits 10 [ones, tens] / 10 = tens := by
          rw [h.symm, this.symm]
          have eq : n = tens * 10 + ones := by
            rw [this, h, Nat.ofDigits_eq_foldr]
            simp
            rw [add_comm, mul_comm]
          apply Nat.div_eq_of_lt_le
          linarith
          rw [eq, hn'.symm]
          have : ones < 10 := by
            apply Nat.digits_lt_base'
            rw [hl.symm, h]
            simp
          linarith
        rw [this]
        omega

    . rintro (hn' | hn')
      . -- n % 10 = 6
        obtain ⟨k, hk⟩ := (by omega: 10 ∣ n - 6)
        have : n = 10 * k + 6 := by omega
        rw [this]
        simp
        apply Or.inl
        omega
      . -- (n / 10) % 10 = 6
        have left : n ≥ 60 := by omega
        have right: n ≤ 69 := by omega
        have : ∃k < 10, n = 60 + k := by
          use (n - 60)
          omega
        obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := this
        rw [hk₂]
        simp
        apply Or.inr
        have : (60 + k) / 10 = 6 := by omega
        rw [this]
        simp

  -- then, if n not in { 16, 26, ..., 86, 96, 60, 61, ..., 69 }, List.count 6 (Nat.digits 10 n) = 0
  have : ∃(S₁ : Finset ℕ), S₁ = {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 6 ∈ (Nat.digits 10 n)} := by
    apply Set.Finite.exists_finset_coe
    have : ((Finset.Icc 10 99) : Set ℕ).Finite := by exact Finset.finite_toSet (Finset.Icc 10 99)
    apply Set.Finite.subset this
    apply Set.sep_subset
  obtain ⟨S₁, hS₁⟩ := this
  have : ∃(S₂ : Finset ℕ), S₂ = {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 6 ∉ (Nat.digits 10 n)} := by
    apply Set.Finite.exists_finset_coe
    have : ((Finset.Icc 10 99) : Set ℕ).Finite := by exact Finset.finite_toSet (Finset.Icc 10 99)
    apply Set.Finite.subset this
    apply Set.sep_subset
  obtain ⟨S₂, hS₂⟩ := this

  have : Finset.Icc 10 99 = S₁ ∪ S₂ := by
    ext n
    simp
    have : n ∈ S₁ ↔ n ∈ (S₁ : Set ℕ) := by rfl
    rw [this, hS₁]
    have : n ∈ S₂ ↔ n ∈ (S₂ : Set ℕ) := by rfl
    rw [this, hS₂]
    simp
    constructor
    . intro hn
      apply and_or_left.mp
      use hn
      exact Decidable.em (6 ∈ Nat.digits 10 n)
    . intro hn
      omega
  rw [this, Finset.sum_union]
  have : ∑n in S₂, List.count 6 (Nat.digits 10 n) = 0 := by
    have (n : ℕ) : n ∈ S₂ ↔ n ∈ (S₂ : Set ℕ) := by rfl
    simp
    intro n hn
    rw [this, hS₂] at hn
    simp at hn
    exact List.count_eq_zero_of_not_mem hn.2

  rw [this]
  have : S₁  = {16, 26, 36, 46, 56, 76, 86, 96, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69} := by
    have (n : ℕ) : n ∈ S₁ ↔ n ∈ (S₁ : Set ℕ) := by rfl
    ext n
    rw [this, hS₁]
    simp
    constructor
    . rintro ⟨⟨hn₁, hn₂⟩, hn₃⟩
      apply (eq_iff n hn₂).mp at hn₃
      revert hn₃
      revert hn₂ hn₁ n
      decide
    . intro hn
      use (by omega)
      apply (eq_iff n (by omega)).mpr
      omega

  rw [this]
  simp
  apply Finset.disjoint_coe.mp
  apply Set.disjoint_left.mpr
  rw [hS₁, hS₂]
  simp
  repeat intro
  assumption
