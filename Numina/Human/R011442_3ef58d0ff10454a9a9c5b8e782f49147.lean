import Mathlib

/-Consider four-digit numbers with the hundreds digit as $3$. If the remainder when the number is divided by $11$ is $1$, find the maximum value of the sum of the digits of the number.


-/
theorem number_theory_633736 : IsGreatest {k | ∃ n, (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n)[2]! = 3 ∧ n % 11 = 1 ∧ k = (Nat.digits 10 n).sum} 26 := by
  constructor
  · use 9395
    native_decide
  · -- Show that if $k$ is in the set and $k > 26$, then $k$ cannot exist.
    set s := Finset.filter (λn ↦ (Nat.digits 10 n)[2]! = 3 ∧ n % 11 = 1) (Finset.Icc 1000 9999) with hs
    have : {k | ∃ n, (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n)[2]! = 3 ∧ n % 11 = 1 ∧ k = (Nat.digits 10 n).sum} = Finset.filter (λk ↦ ∃ n ∈ s, k = (Nat.digits 10 n).sum) (Finset.Icc 0 36):= by
      rw [hs]; ext x; simp only [Nat.reduceLeDiff, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero, Finset.mem_filter, Finset.mem_Icc, Finset.coe_filter, zero_le, true_and, Nat.reduceLeDiff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn1, hn2, hn3, hx1⟩
        have : x ≤ 36 := by
          rw [hx1]
          suffices (Nat.digits 10 n).sum ≤ 9 * (Nat.digits 10 n).length by linarith
          have (l : List ℕ) (hl : ∀i ∈ l, i < 10) : l.sum ≤ 9 * l.length := by
            induction' l with x xs ih
            · simp
            · simp only [List.sum_cons, List.length_cons]
              have : ∀ i ∈ xs, i < 10 := by
                intro i hi
                apply hl i (by simp [hi])
              specialize hl x (by simp)
              specialize ih this
              omega
          apply this (Nat.digits 10 n)
          intro i hi
          apply Nat.digits_lt_base (by omega) hi
        use this
        use n
        clear this
        have : 1000 ≤ n ∧ n ≤ 9999 := by
          rw [Nat.digits_len _ _ (by omega) (by omega)] at hn1
          simp only [Nat.reduceEqDiff] at hn1
          rw [Nat.log_eq_iff] at hn1
          all_goals omega
        simp only [this, and_self, Nat.reduceLeDiff, true_and]
        split_ands
        all_goals assumption
      · rintro ⟨hx1, n, ⟨hn1, hn2, hn3⟩, hx2⟩
        use n
        have : (Nat.digits 10 n).length = 4 := by
          rw [Nat.digits_len _ _ (by omega) (by omega)]
          simp only [Nat.reduceEqDiff]
          apply Nat.log_eq_of_pow_le_of_lt_pow
          all_goals omega
        simp only [this, and_self, Nat.reduceLeDiff, true_and]
        split_ands
        all_goals assumption
    rw [this]
    have : Finset.filter (λk ↦ ∃ n ∈ s, k = (Nat.digits 10 n).sum) (Finset.Icc 0 36) = {5, 7, 9, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26} := by
      rw [hs]
      native_decide
    rw [this]
    simp
