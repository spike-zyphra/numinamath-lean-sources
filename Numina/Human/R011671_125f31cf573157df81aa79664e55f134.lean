import Mathlib

/-Let $f$ be the function that associates with a positive integer the sum of its digits when it is written in base 10. For example, $f(537)=15$. Calculate $f\left(f\left(f\left(4444^{4444}\right)\right)\right)$.-/
theorem number_theory_144357 {f : ℕ → ℕ} (h : f = λn ↦ (Nat.digits 10 n).sum) :
    f (f (f (4444 ^ 4444))) = 7 := by
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
  have hf₃ : f (f (f (4444 ^ 4444))) ≤ 13 := by
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
    apply this _ h₃
  have hf₄ : f (f (f (4444 ^ 4444))) ≡ 7 [MOD 9] := by
    apply Nat.ModEq.trans (hf₁ (f (f (4444 ^ 4444))))
    apply Nat.ModEq.trans (hf₁ (f (4444 ^ 4444)))
    apply Nat.ModEq.trans (hf₁ (4444 ^ 4444))
    rw [Nat.ModEq]
    norm_num
  rw [Nat.ModEq] at hf₄
  omega
