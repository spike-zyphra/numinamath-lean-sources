import Mathlib

/-1- 17 Let $A$ be the sum of the digits of the decimal number $4444^{4444}$, and let $B$ be the sum of the digits of $A$. Find the sum of the digits of $B$ (all numbers here are in decimal)..-/
theorem number_theory_144357 {A B C : ℕ} (hA : A = (Nat.digits 10 (4444 ^ 4444)).sum) (hB : B = (Nat.digits 10 A).sum) (hC : C = (Nat.digits 10 B).sum) : C = 7 := by
  set f := fun n => (Nat.digits 10 n).sum with h
  have hA' : A = f (4444 ^ 4444) := by rw [hA]
  have hB' : B = f A := by rw [hB]
  have hC' : C = f B := by rw [hC]
  have hf₁ : ∀n, f n ≡ n [MOD 9] := by
    intro n
    rw [h]
    simp
    exact Nat.ModEq.symm (Nat.modEq_nine_digits_sum n)
  have hf₂ : ∀n, f n ≤ 9 * (Nat.digits 10 n).length := by
    intro n
    rw [h]
    simp
    set l := Nat.digits 10 n with hl₁
    have hl₂ : ∀i ∈ l, i ≤ 9 := by
      rw [hl₁]
      intro i hi
      suffices i < 10 by omega
      apply Nat.digits_lt_base
      exact (by omega)
      exact hi
    have : 9 * l.length = (List.replicate l.length 9).sum := by
      simp
      ring_nf
    rw [this]
    revert hl₂
    induction' l with h t ih
    · simp
    · simp
      intro h₁ h₂
      specialize ih h₂
      simp at ih ⊢
      omega
  have hf₃ : C ≤ 13 := by
    have hf₂' : ∀n, f n ≤ 9 * (Nat.log 10 n + 1) := by
      intro n
      by_cases h₁ : n = 0
      · rw [h₁, h]
        simp
      specialize hf₂ n
      rw [Nat.digits_len] at hf₂
      exact hf₂
      repeat omega
    have h₁ : f (4444 ^ 4444) ≤ 9 * (Nat.log 10 (4444 ^ 4444) + 1) := by
      apply hf₂'
    have h₂ : f (4444 ^ 4444) ≤ 199989 := by
      apply le_trans h₁
      suffices (9 * (Nat.log 10 (4444 ^ 4444) + 1) : ℝ) ≤ 199989 by norm_cast at this
      suffices 9 * (Real.logb 10 (4444 ^ 4444 : ℕ) + 1) ≤ 199989 by
        apply le_trans ?_ this
        rw [mul_le_mul_left (by positivity), add_le_add_iff_right]
        apply Real.natLog_le_logb
      rw [Nat.cast_pow, Real.logb_pow]
      ring_nf
      have : Real.logb 10 4444 < 5 := by
        have : 5 = Real.logb 10 (10^5) := by
          rw [Real.logb_pow]
          norm_num
        rw [this]
        apply Real.logb_lt_logb
        repeat linarith
      linarith
    have h₃ : f (f (4444 ^ 4444)) ≤ 9 * (Nat.log 10 (199989) + 1) := by
      apply le_trans (hf₂' (f (4444 ^ 4444)))
      have : Nat.log 10 (f (4444 ^ 4444)) ≤ Nat.log 10 (199989) := by
        apply Nat.log_mono_right
        exact h₂
      linarith
    rw [show 9 * (Nat.log 10 (199989) + 1) = 54 by native_decide] at h₃
    have : ∀n ≤ 54, f n ≤ 13 := by
      rw [h]
      simp
      intro n hn
      interval_cases n <;> norm_num
    rw [hC', hB', hA']
    apply this
    linarith
  have hf₄ : C ≡ 7 [MOD 9] := by
    rw [hC', hB', hA']
    apply Nat.ModEq.trans (hf₁ (f (f (4444 ^ 4444))))
    apply Nat.ModEq.trans (hf₁ (f (4444 ^ 4444)))
    apply Nat.ModEq.trans (hf₁ (4444 ^ 4444))
    rw [Nat.ModEq]
    norm_num
  rw [Nat.ModEq] at hf₄
  omega
