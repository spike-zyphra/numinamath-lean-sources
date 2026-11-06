import Mathlib

def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => 2 * a (n + 1) + a n

theorem other_24110 (n k : ℕ) : 2 ^ k ∣ a n ↔ 2 ^ k ∣ n := by
  -- Prove that a (2n + 1) is odd for all n.
  have h₀ (n : ℕ) : a (2 * n + 1) ≡ 1 [MOD 2] := by
    induction n with
    | zero =>
      simp [a]
      rfl
    | succ n hn =>
      simp [a]
      calc
        2 * (2 * a (2 * n + 1) + a (2 * n)) + a (2 * n + 1) ≡ 2 * (2 * a (2 * n + 1) + a (2 * n)) + 1 [MOD 2] := Nat.ModEq.add_left _ hn
        _ ≡ 1 [MOD 2] := by symm; rw [Nat.modEq_iff_dvd']; omega; omega
  -- Prove that a (2n) is even for all n.
  have h₁ (n : ℕ) : a (2 * n) ≡ 0 [MOD 2] := by
    induction n with
    | zero =>
      simp [a]
      rfl
    | succ n hn =>
      simp [a]
      calc
        2 * a (2 * n + 1) + a (2 * n) ≡ 2 * a (2 * n + 1) + 0 [MOD 2] := by apply Nat.ModEq.add_left; exact hn
        _ ≡ 0 [MOD 2] := by symm; rw [Nat.modEq_iff_dvd']; omega; omega
  -- Prove that a (2n + 1) = a (n + 1) ^ 2 + a n ^ 2 and a (2n + 2) = 2 * a (n + 1) * (a (n + 1) + a n) for all n.
  have h₂ (n : ℕ) : a (2 * n + 1) = a (n + 1) ^ 2 + a n ^ 2 ∧ a (2 * n + 2) = 2 * a (n + 1) * (a (n + 1) + a n) := by
    induction n with
    | zero =>
      simp [a]
    | succ n hn =>
      have h₂ : a (2 * (n + 1) + 1) = a (n + 1 + 1) ^ 2 + a (n + 1) ^ 2 := by
        rw [show a (2 * (n + 1) + 1) = 2 * a (2 * n + 2) + a (2 * n + 1) by simp [a]]
        rw [hn.1, hn.2, show a (n + 1 + 1) = 2 * a (n + 1) + a n by simp [a]]
        ring
      refine ⟨h₂, ?_⟩
      rw [show a (2 * (n + 1) + 2) = 2 * a (2 * (n + 1) + 1) + a (2 * n + 2) by simp [a]]
      rw [h₂, hn.2, show a (n + 1 + 1) = 2 * a (n + 1) + a n by simp [a]]
      ring
  -- Prove the main goal.
  induction k generalizing n with
  | zero =>
    simp
  | succ k hk =>
    -- Break the iff into two implications.
    by_cases hn₀ : n = 0
    . simp [hn₀, a]
    . apply Iff.intro
      <;> intro hn₁
      . by_contra hn₂
        by_cases hn₃ : k = 0
        . -- If k = 0, use h₀ to derive the goal.
          simp only [hn₃, zero_add, pow_one] at hn₁ hn₂
          rw [<-even_iff_two_dvd] at hn₂
          simp [Odd] at hn₂
          obtain ⟨m, hn₂⟩ := hn₂
          replace h₀ := (h₀ m).symm
          rw [<-hn₂] at h₀
          have weq : 0 ≡ 1 [MOD 2] := by
            calc
              0 ≡ a n [MOD 2] := by rw [Nat.modEq_iff_dvd']; apply hn₁; omega
              _ ≡ 1 [MOD 2] := h₀.symm
          rw [Nat.modEq_iff_dvd'] at weq
          omega
          norm_num
        . -- If k > 0, write a n = 2 * a (n / 2) * (a (n / 2) + a (n / 2 - 1)) to use the induction hypothesis.
          have hn₄ : 2 ^ k ∣ a n := by
            exact (Nat.pow_dvd_pow 2 (by omega)).trans hn₁
          simp [hk n] at hn₄
          have hn₅ : 2 ^ 1 ∣ n := by
            exact (Nat.pow_dvd_pow 2 (by omega)).trans hn₄
          simp at hn₅
          rw [dvd_iff_exists_eq_mul_right] at hn₅
          obtain ⟨m, hn₅⟩ := hn₅
          replace hn₆ : m ≥ 1 := by
            omega
          replace h₂ := (h₂ (m - 1)).2
          rw [show 2 * (m - 1) + 2 = n by omega, Nat.sub_add_cancel hn₆] at h₂
          rw [h₂, Nat.pow_add, Nat.pow_one, Nat.mul_comm, Nat.mul_assoc] at hn₁
          apply Nat.dvd_of_mul_dvd_mul_left (by norm_num) at hn₁
          apply Prime.pow_dvd_of_dvd_mul_right at hn₁
          pick_goal 2
          . rw [<-Nat.prime_iff]
            exact Nat.prime_two
          pick_goal 2
          . rw [<-Nat.modEq_zero_iff_dvd]
            by_contra! hn₇
            by_cases hn₈ : Odd m
            . simp [Odd] at hn₈
              obtain ⟨m', hn₈⟩ := hn₈
              rw [hn₈, Nat.add_sub_cancel] at hn₇
              have weq : 0 ≡ 1 [MOD 2] := by
                calc
                  0 ≡ a (2 * m' + 1) + a (2 * m') [MOD 2] := hn₇.symm
                  _ ≡ 1 + 0 [MOD 2] := by apply Nat.ModEq.add; exact h₀ m'; exact h₁ m'
                  _ ≡ 1 [MOD 2] := by norm_num; rfl
              rw [Nat.modEq_iff_dvd'] at weq
              omega
              norm_num
            . simp [even_iff_two_dvd] at hn₈
              rw [dvd_iff_exists_eq_mul_right] at hn₈
              obtain ⟨m', hn₈⟩ := hn₈
              rw [hn₈] at hn₇
              have weq : 0 ≡ 1 [MOD 2] := by
                calc
                  0 ≡ a (2 * m') + a (2 * (m' - 1) + 1) [MOD 2] := by rw [show 2 * (m' - 1) + 1 = 2 * m' - 1 by omega]; exact hn₇.symm
                  _ ≡ 0 + 1 [MOD 2] := by apply Nat.ModEq.add; exact h₁ m'; exact h₀ (m' - 1)
                  _ ≡ 1 [MOD 2] := by norm_num; rfl
              rw [Nat.modEq_iff_dvd'] at weq
              omega
              norm_num
          simp [hk m] at hn₁
          absurd hn₂
          calc
            2 ^ (k + 1) ∣ 2 * m := by rw [Nat.add_comm, Nat.pow_add]; apply Nat.mul_dvd_mul_left _ hn₁
            _ = n := hn₅.symm
      . simp [Nat.pow_add] at hn₁ ⊢
        have hn₂ : 2 ∣ n := by
          exact (Nat.dvd_mul_left _ _).trans hn₁
        rw [dvd_iff_exists_eq_mul_right] at hn₂
        obtain ⟨m, hn₂⟩ := hn₂
        replace hn₀ : m ≥ 1 := by
          omega
        rw [hn₂, show 2 * m = 2 * (m - 1) + 2 by omega, (h₂ (m - 1)).2, Nat.sub_add_cancel hn₀]
        rw [hn₂, Nat.mul_comm] at hn₁
        apply Nat.dvd_of_mul_dvd_mul_left at hn₁
        rw [(hk m).symm] at hn₁
        rw [Nat.mul_comm, Nat.mul_assoc]
        apply Nat.mul_dvd_mul_left
        exact hn₁.trans (Nat.dvd_mul_right _ _)
        norm_num
