import Mathlib

/- What is the largest whole number that is equal to the product of its digits?-/
theorem number_theory_611217 :
    IsGreatest {n : ℕ | n = (Nat.digits 10 n).prod} 9 := by
  -- Show a general lemma.
  have hlm {n : ℕ} (hn : n ≠ 0) : n / 10 ^ (Nat.log 10 n) = (Nat.digits 10 n)[Nat.log 10 n]! := by
    -- Show that n belongs to the range of [10 ^ Nat.log 10 n, 10 ^ (Nat.log 10 n + 1)).
    replace hn : n ∈ Finset.Ico (10 ^ Nat.log 10 n) (10 ^ (Nat.log 10 n + 1)) := by
      simp
      rw [<-Nat.log_eq_iff]
      simp [hn]
    -- We try to generalize k = Nat.log 10 n and do induction on k with n ∈ [10 ^ k, 10 ^ (k + 1)).
    revert hn
    obtain k := Nat.log 10 n
    revert n
    simp
    induction k with
    | zero =>
      -- Case k = 0.
      intro n _ _
      have h₀ := Nat.digits_len 10 n (by norm_num) (by omega)
      rw [Nat.log_eq_zero_iff.mpr (by omega)] at h₀
      obtain ⟨m, h₀⟩ := List.length_eq_one.mp h₀
      have h₁ := (Nat.ofDigits_digits 10 n).symm
      simp [h₀] at h₁ ⊢
      assumption
    | succ k hk =>
      -- Inductive case.
      intro n _ _
      have h₀ := @Nat.digits_eq_cons_digits_div 10 n (by norm_num) (by omega)
      simp [h₀, show n / 10 ^ (k + 1) = (n / 10) / 10 ^ k by rw [Nat.div_div_eq_div_mul, Nat.pow_succ']]
      apply hk
      <;> omega
  -- Simplify the goal.
  simp [IsGreatest, upperBounds]
  -- It suffices to show that 9 is an upper bound.
  intro n hn
  -- Assume on the contrary that n > 9.
  by_contra! hn'
  -- Let k be one less than the number of digits of n.
  let k := Nat.log 10 n
  have hk : k + 1 = (Nat.digits 10 n).length := by
    simp [k, Nat.digits_len 10 n (by norm_num) (by omega)]
  -- Let d = n / 10 ^ k.
  let d := n / 10 ^ k
  -- Show that n ≥ d * 10 ^ k.
  have hd : n ≥ d * 10 ^ k := by
    simp [d]
    apply Nat.div_mul_le_self
  -- Show that the product of digits ≤ d * 9 ^ k.
  have h₁ : (Nat.digits 10 n).prod ≤ d * 9 ^ k := by
    -- Show that the product of digits is at most 9 ^ k.
    specialize hlm (show n ≠ 0 by omega)
    rw [<-List.take_append_getLast (Nat.digits 10 n) (by simp [Nat.digits_ne_nil_iff_ne_zero]; omega), <-hk, <-List.getElem_length_sub_one_eq_getLast _ (by rw [<-hk]; omega)]
    simp [<-hk]
    rw [show Nat.log 10 n = k by rfl, show n / 10 ^ k = d by rfl] at *
    have : (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[k] := by
      rw [List.getElem!_eq_getElem?_getD, getElem?_def]
      simp [show k < (Nat.digits 10 n).length by rw [<-hk]; omega]
    rw [<-this, <-hlm, mul_comm]
    apply Nat.mul_le_mul_left
    nth_rw 2 [show k = (List.take k (Nat.digits 10 n)).length by simp [<-hk]]
    apply List.prod_le_pow_card
    intro x hx
    suffices x < 10 by
      omega
    apply @Nat.digits_lt_base 10 n _ (by norm_num)
    exact List.mem_of_mem_take hx
  -- Now we have d * 10 ^ k ≤ d * 9 ^ k, which is a contradiction.
  have h₂ : d * 10 ^ k ≤ d * 9 ^ k := by
    calc
      _ ≤ n := hd
      _ ≤ d * 9 ^ k := by
        rw [hn]
        exact h₁
  have hd' : 0 < d := by
    simp [d, k]
    suffices 10 ^ Nat.log 10 n ≤ n ∧ n < 10 ^ (Nat.log 10 n + 1) by
      tauto
    rw [<-Nat.log_eq_iff]
    simp
    omega
  have hk' : k ≠ 0 := by
    by_contra!
    simp [this] at hk
    obtain ⟨m, h₃⟩ := List.length_eq_one.mp hk.symm
    have h₄ := (Nat.ofDigits_digits 10 n).symm
    simp [h₃] at h₄
    absurd hn'
    suffices n < 10 by
      omega
    apply @Nat.digits_lt_base 10 n _ (by norm_num)
    rw [h₃, <-h₄]
    simp
  replace h₂ := Nat.le_of_mul_le_mul_left h₂ hd'
  rw [Nat.pow_le_pow_iff_left hk'] at h₂
  norm_num at h₂
  