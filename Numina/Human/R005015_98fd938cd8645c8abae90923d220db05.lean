import Mathlib

/- Show that there are arbitrarily large numbers $n$ such that: (1) all its digits are 2 or more; and (2) the product of any four of its digits divides $n$. -/

theorem number_theory_605080 :
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧
  (∀ d ∈ Nat.digits 10 n, d ≥ 2) ∧
  (∀ i j k l : Fin (Nat.digits 10 n).length, i < j ∧ j < k ∧ k < l →
  (Nat.digits 10 n)[i]! * (Nat.digits 10 n)[j]! * (Nat.digits 10 n)[k]! * (Nat.digits 10 n)[l]! ∣ n) := by

  intro N

  let Nlength := (Nat.digits 10 N).length
  let nlist := [2, 3, 2, 3] ++ List.replicate (Nlength * 9 + 4) 2
  let n := Nat.ofDigits 10 nlist

  have h_nlist : Nat.digits 10 n = nlist := by
    rw [Nat.digits_ofDigits]
    . norm_num
    . intro l hl
      unfold nlist at hl
      simp at hl
      omega
    . intro h
      unfold nlist
      simp

  have hn_ne_zero : n ≠ 0 := by
    rw [← Nat.digits_ne_nil_iff_ne_zero]
    rw [h_nlist]
    unfold nlist
    simp

  use n
  let nlength := nlist.length
  let x := 10 ^ (nlength - 1)

  constructor
  ·-- show that N is less than n as we constructed n in a way that has way more digits than N.
    have h1 : N < 10 ^ Nlength := by
      by_cases hN : N = 0
      . subst N
        simp
      . unfold Nlength
        rw [Nat.digits_len]
        . rw [← Nat.succ_eq_add_one]
          apply Nat.lt_pow_succ_log_self
          norm_num
        . norm_num
        . exact hN
    have h2 : 10^Nlength < 10^(nlength-1) := by
      apply Nat.pow_lt_pow_right
      . norm_num
      . unfold nlength nlist
        simp
        omega

    have h3 : 10 ^ (nlength - 1) ≤ n := by
      unfold nlength
      rw [← h_nlist]
      rw [Nat.digits_len]
      . simp
        apply Nat.pow_log_le_self
        exact hn_ne_zero
      . norm_num
      . exact hn_ne_zero

    linarith

  · constructor
    · intro d hd
      -- every digit of n is at least 2.
      -- show 2 ≤ every element in nlist
      rw [h_nlist] at hd
      unfold nlist at hd
      simp at hd
      omega

    · intros i j k l h_distinct
      -- there are three possibilities
      -- all digits are 2
      -- three digits are 2, one is 3
      -- two digits are 2, two digits are 3
      -- show that in either case, the product of them divides n

      have h_9_dvd_n : 9 ∣ n := by
        rw [Nat.nine_dvd_iff]
        rw [h_nlist]
        unfold nlist
        simp
        omega

      have h_16_dvd_n : 16 ∣ n := by
        unfold n nlist
        let n2 := Nat.ofDigits 10 (List.replicate (Nlength * 9 + 4) 2)
        have h_n2 : Nat.digits 10 n2 = List.replicate (Nlength * 9 + 4) 2 := by
          rw [Nat.digits_ofDigits]
          . norm_num
          . intro l hl
            unfold nlist at hl
            simp at hl
            omega
          . intro h
            simp
        have := @Nat.ofDigits_digits_append_digits 10 n2 3232
        rw [h_n2, show Nat.digits 10 3232 = [2, 3, 2, 3] by norm_num] at this
        rw [this, show [2, 3, 2, 3].length = 4 by norm_num]
        omega

      have h_24_dvd_n : 24 ∣ n := by
        omega

      have h_36_dvd_n : 36 ∣ n := by
        omega

      have h_eq3: ∀ m : Fin (Nat.digits 10 n).length, m.val = 1 ∨ m.val = 3 → (Nat.digits 10 n)[m]! = 3 := by
        rintro m (hm | hm)
        all_goals
        . simp [hm, h_nlist]
          unfold nlist
          simp

      have h_eq2 : ∀ m : Fin (Nat.digits 10 n).length, (m.val = 0 ∨ m.val = 2 ∨ 4 ≤ m.val) → (Nat.digits 10 n)[m]! = 2 := by
        rintro m (hm | hm | hm)
        . simp [hm, h_nlist]
          unfold nlist
          simp
        . simp [hm, h_nlist]
          unfold nlist
          simp
        . simp
          simp [h_nlist]
          unfold nlist
          rw [List.getElem_append_right]
          . simp
          . simp
            exact hm

      by_cases hi1 : 4 ≤ i.val
      . rw [h_eq2 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
      . simp at hi1
        by_cases hi2 : i.val = 3
        . rw [h_eq3 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
        . by_cases hi3 : i.val = 2
          . by_cases hj1 : 4 ≤ j.val
            . rw [h_eq2 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
            . have hj2 : j.val = 3 := by omega
              rw [h_eq2 i, h_eq3 j, h_eq2 k, h_eq2 l] <;> omega
          . by_cases hi4 : i.val = 1
            . by_cases hj1 : 4 ≤ j.val
              . rw [h_eq3 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
              . by_cases hj2 : j.val = 3
                . rw [h_eq3 i, h_eq3 j, h_eq2 k, h_eq2 l] <;> omega
                . have hj3 : j.val = 2 := by omega
                  by_cases hk1 : 4 ≤ k.val
                  . rw [h_eq3 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
                  . have hk2 : k.val = 3 := by omega
                    rw [h_eq3 i, h_eq2 j, h_eq3 k, h_eq2 l] <;> omega
            . have hi5 : i.val = 0 := by omega
              by_cases hj1 : 4 ≤ j.val
              . rw [h_eq2 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
              . by_cases hj2 : j.val = 3
                . rw [h_eq2 i, h_eq3 j, h_eq2 k, h_eq2 l] <;> omega
                . by_cases hj3 : j.val = 2
                  . by_cases hk1 : 4 ≤ k.val
                    . rw [h_eq2 i, h_eq2 j, h_eq2 k, h_eq2 l] <;> omega
                    . by_cases hk2 : k.val = 3
                      . rw [h_eq2 i, h_eq2 j, h_eq3 k, h_eq2 l] <;> omega
                      . have hl1 : 4 ≤ l.val := by omega
                        rw [h_eq2 i, h_eq2 j, h_eq3 k, h_eq2 l] <;> omega
                  . have hj4 : j.val = 1 := by omega
                    by_cases hk1 : 4 ≤ k.val
                    . rw [h_eq2 i, h_eq3 j, h_eq2 k, h_eq2 l] <;> omega
                    . by_cases hk2 : k.val = 3
                      . rw [h_eq2 i, h_eq3 j, h_eq3 k, h_eq2 l] <;> omega
                      . have hk3 : k.val = 2 := by omega
                        by_cases hl1 : 4 ≤ l.val
                        . rw [h_eq2 i, h_eq3 j, h_eq2 k, h_eq2 l] <;> omega
                        . have hl2 : l.val = 3 := by omega
                          rw [h_eq2 i, h_eq3 j, h_eq2 k, h_eq3 l] <;> omega
