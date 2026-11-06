import Mathlib


lemma sum_1_to_9_eq_45 {n : ℕ} : (∑ i ∈ Finset.Icc 1 9, i * n) = 45 * n := by
  rw [← Finset.sum_mul]
  rw [show (∑ i ∈ Finset.Icc 1 9, i) = 45 by native_decide]

lemma ofDigits_replicate_zero (b n : ℕ) : Nat.ofDigits b (List.replicate n 0) = 0 := by
  induction n with
  | zero =>
    rw [List.replicate_zero, Nat.ofDigits_nil]
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih]
    norm_num

theorem number_theory_88630
  (N : ℕ) (hN : IsLeast {x | 0 < x ∧ ∃ k, ∑ i ∈ Finset.Icc 1 9, i * x = k ∧ ∃ c ≤ 9, ∀ d ∈ Nat.digits 10 k, d = c} N):
  (Nat.digits 10 N).sum = 37 := by

  suffices N = 12345679 by
    rw [this]
    native_decide

  suffices IsLeast {x | 0 < x ∧ ∃ k, ∑ i ∈ Finset.Icc 1 9, i * x = k ∧ ∃ c ≤ 9, ∀ d ∈ Nat.digits 10 k, d = c} 12345679 from
    IsLeast.unique hN this

  constructor
  . simp
    use 5
    simp
    intro d hd
    rw [sum_1_to_9_eq_45] at hd
    simp at hd
    exact hd

  . unfold lowerBounds
    simp
    intro x hx_pos c hc hx
    rw [sum_1_to_9_eq_45] at hx
    by_cases h_even : x % 2 = 0
    . have : 0 ∈ Nat.digits 10 (45 * x) := by
        rw [Nat.digits_of_two_le_of_pos (show 2 ≤ 10 by norm_num) (show 0 < 45 * x by omega)]
        simp
        left
        omega

      have : c = 0 := (hx 0 this).symm
      subst c
      replace hx := List.eq_replicate_of_mem hx

      have h1: 45 * x = Nat.ofDigits 10 (Nat.digits 10 (45 * x)) := by
        rw [Nat.ofDigits_digits]

      rw [hx] at h1
      rw [ofDigits_replicate_zero 10 (Nat.digits 10 (45 * x)).length] at h1
      omega

    . have : x % 2 = 1 := by omega
      have : 5 ∈ Nat.digits 10 (45 * x) := by
        rw [Nat.digits_of_two_le_of_pos (show 2 ≤ 10 by norm_num) (show 0 < 45 * x by omega)]
        simp
        left
        omega

      have : c = 5 := (hx 5 this).symm
      subst c

      replace hx := List.eq_replicate_of_mem hx

      have h1: 45 * x = Nat.ofDigits 10 (Nat.digits 10 (45 * x)) := by
        rw [Nat.ofDigits_digits]

      rw [hx] at h1

      have h2: 9 ∣ 45 * x := by omega

      rw [h1] at h2

      rw [Nat.nine_dvd_iff] at h2
      rw [Nat.digits_ofDigits] at h2
      . simp at h2
        replace h2 : 9 ∣ (Nat.digits 10 (45 * x)).length := by omega
        apply Nat.le_of_dvd at h2
        . by_contra h_contra
          replace h_contra : 45 * x < 555555555 := by omega
          rw [Nat.digits_len] at h2
          . replace h2 : 8 ≤ Nat.log 10 (45 * x) := by omega
            have h3 : 10 ^ 8 ≤ 10 ^ (Nat.log 10 (45 * x)) := by
              apply Nat.pow_le_pow_right
              . norm_num
              . exact h2
            have h4 := Nat.pow_log_le_self 10 (show 45 * x ≠ 0 by omega)
            have h5 : 10 ^ 8 ≤ 45 * x := by linarith
            have h6 : (Nat.digits 10 (45 * x)).length = 9 := by
              rw [Nat.digits_len]
              . simp
                have := @Nat.log_mono_right 10 (45 * x) 555555555 (by omega)
                rw [show Nat.log 10 555555555 = 8 by native_decide] at this
                omega
              . omega
              . omega

            rw [h6] at h1
            simp at h1
            have : 45 * x = 555555555 := by
              rw [h1]
              native_decide

            rw [this] at h_contra
            norm_num at h_contra

          . omega
          . omega

        . rw [Nat.digits_len]
          . simp
          . omega
          . omega

      . norm_num
      . intro l hl
        simp at hl
        omega
      . intro h
        simp
