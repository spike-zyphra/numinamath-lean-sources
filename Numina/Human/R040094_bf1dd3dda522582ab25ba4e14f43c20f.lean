import Mathlib

/-How many fractions in the form $\frac{n}{99}$, with $0<n<99$, are in lowest terms?-/
theorem number_theory_22894 :
  Set.encard {n | 0 < n ∧ n < 99 ∧ Nat.Coprime n 99} = 60 := by
    -- Auxiliary lemma : the number n is coprime with 99 iff ¬ (3 ∣ n ∨ 11 ∣ n).
    have h1 {n : ℕ} : Nat.Coprime n 99 ↔ ¬ (3 ∣ n ∨ 11 ∣ n) := by
      constructor
      · intro h
        contrapose! h
        rcases h with h | h
        <;> exact Nat.not_coprime_of_dvd_of_dvd (by omega) h (by omega)
      · intro h
        apply Nat.Coprime.symm
        apply Nat.coprime_of_dvd
        intro k kprime kdvd
        have : k = 3 ∨ k = 11 := by
          rw [show 99 = 3^2 * 11 by omega] at kdvd
          rcases (Nat.Prime.dvd_mul kprime).1 kdvd with h1 | h1
          · left; rw [pow_two, Nat.Prime.dvd_mul kprime] at h1
            simp at h1
            rw [Nat.dvd_prime (by norm_num)] at h1
            simp [Nat.Prime.ne_one kprime] at h1
            assumption
          · right
            rw [Nat.dvd_prime (by norm_num)] at h1
            simp [Nat.Prime.ne_one kprime] at h1
            assumption
        rcases this with h1 | h1 <;> simp [h1] <;> tauto
    -- the number of elements of {n | 0 < n ∧ n < 99 ∧ (3 ∣ n ∨ 11 ∣ n)} is 38.
    have h2 : Set.encard {n | 0 < n ∧ n < 99 ∧ (3 ∣ n ∨ 11 ∣ n)} = 38 := by
      simp [and_or_left, Set.setOf_or]
      let s3  := {a | 0 < a ∧ a < 99 ∧ 3 ∣ a}
      let s11 := {a | 0 < a ∧ a < 99 ∧ 11 ∣ a}
      have := Set.encard_union_add_encard_inter s3 s11
      have h2 : (s3 ∩ s11).encard = 2 := by
        suffices s3 ∩ s11 = {33, 66} by
          rw [this, Set.encard_pair (by omega)]
        simp [s3, s11]
        ext x
        simp
        constructor
        · intro ⟨ ⟨h11, h12, h13⟩, ⟨h21, h22, h23⟩ ⟩
          interval_cases x <;> norm_num at h13 h23 <;> tauto
        · intro hx
          rcases hx with hx | hx <;> norm_num [hx]
       -- the number of elements of {a | 0 < a ∧ a < 99 ∧ 3 ∣ a} is 32.
      have h3 : s3.encard = 32 := by
        have : s3 ≃ Fin 32 := {
          toFun := fun x => ⟨x.1 / 3 - 1, by
            have := Set.mem_setOf.1 x.2
            omega⟩
          invFun := fun x => ⟨(x.1 + 1) * 3, by simp [s3]; omega⟩ 
          left_inv := fun x => by
            simp; ext; simp
            rw [Nat.sub_add_cancel , Nat.div_mul_cancel x.2.2.2] 
            have := Set.mem_setOf.1 x.2
            omega
          right_inv := fun x => by simp
        }
        rw [Set.encard_congr <| this.trans ((Equiv.Set.univ (Fin 32)).symm)]
        simp [Set.encard_univ]
      -- the number of elements of {a | 0 < a ∧ a < 99 ∧ 11 ∣ a} is 8.
      have h4 : s11.encard = 8 := by
        have : s11 ≃ Fin 8 := {
          toFun := fun x => ⟨x.1 / 11 - 1, by
            have := Set.mem_setOf.1 x.2
            omega⟩
          invFun := fun x => ⟨(x.1 + 1) * 11, by simp [s11]; omega⟩
          left_inv := fun x => by
            simp; ext; simp
            rw [Nat.sub_add_cancel , Nat.div_mul_cancel x.2.2.2]
            have := Set.mem_setOf.1 x.2
            omega
          right_inv := fun x => by simp
        }
        rw [Set.encard_congr <| this.trans ((Equiv.Set.univ (Fin 8)).symm)]
        simp [Set.encard_univ]
      norm_num [h2, h3, h4] at this
      generalize (s3 ∪ s11).encard = e at *
      induction' e with e ih
      · norm_num  at this
      · norm_cast at this ⊢
        omega
    have h3 : {n | 0 < n ∧ n < 99 ∧ Nat.Coprime n 99} ∪ {n | 0 < n ∧ n < 99 ∧ (3 ∣ n ∨ 11 ∣ n)} = {n | 0 < n ∧ n < 99} := by
      simp only [h1]
      ext x
      simp
      tauto
    have h4 : Disjoint {n | 0 < n ∧ n < 99 ∧ Nat.Coprime n 99} {n | 0 < n ∧ n < 99 ∧ (3 ∣ n ∨ 11 ∣ n)} := by
      rw [Set.disjoint_iff]
      simp [h1]
      ext x
      simp
      tauto
    have h5 : {n | 0 < n ∧ n < 99}.encard = 98 := by
      have  : {n | 0 < n ∧ n < 99} ≃ (Fin 98) := {
        toFun := fun x => ⟨x - 1, by 
          have := Set.mem_setOf.1 x.2
          rw [show 98 = 99 - 1 by omega]
          exact Nat.sub_lt_sub_right (by omega) (by omega)⟩ 
        invFun := fun x => ⟨x.1 + 1, by simp; omega⟩ 
        left_inv := fun x => by simp; ext; simp; have := Set.mem_setOf.1 x.2; rw [Nat.sub_add_cancel (by omega)]
        right_inv := fun x => by simp
      }
      rw [Set.encard_congr <| this.trans ((Equiv.Set.univ (Fin 98)).symm)]
      simp [Set.encard_univ]
    --  So there are $32+8-2=38$ values of $n$ that are divisible by 3 or 11. That means there are $98-38=\boxed{60}$ values of $n$ for which $\frac{n}{99}$ is in lowest terms.
    have h6 := Set.encard_union_eq h4
    simp [h2, h3, h5] at h6
    generalize {n | 0 < n ∧ n < 99 ∧ n.Coprime 99}.encard = e at h6
    induction' e with e ih
    · norm_num  at h6
    · norm_cast at h6 ⊢
      omega


