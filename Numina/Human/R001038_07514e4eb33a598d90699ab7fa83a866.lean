import Mathlib

/- How many integers between 200 and 300 have the sum of their digits equal to 15? -/
theorem algebra_20058 :
    Set.ncard {n : ℕ | 200 ≤ n ∧ n < 300 ∧ (Nat.digits 10 n).sum = 15} = 6 := by
  -- show the set is {267, 276, 258, 285, 249, 294}
  have h : {n : ℕ | 200 ≤ n ∧ n < 300 ∧ (Nat.digits 10 n).sum = 15} = {267, 276, 258, 285, 249, 294} := by
    ext n
    constructor
    . {
      -- prove the set is a subset of {267, 276, 258, 285, 249, 294}
      simp
      intro n_ge_200 n_le_300 sum_eq_15
      -- expand Nat.digits to [a, b, 2]
      have exist_a_b: ∃ a b:ℕ, a < 10 ∧ b < 10 ∧ Nat.digits 10 n = [a, b, 2] := by
        use (n % 10)
        use (n / 10 % 10)
        constructor
        exact Nat.mod_lt n (by norm_num)
        constructor
        exact Nat.mod_lt (n / 10) (by norm_num)
        have n_lt_zero_of_ne_zero {n:ℕ} (h: n ≠ 0): n > 0 := by
          cases n with
          | zero => exfalso; apply h rfl
          | succ a => apply Nat.zero_lt_succ
        -- the ones place is equal to n % 10
        by_cases h : n = 0
        linarith
        rw [Nat.digits_def' (by norm_num) (n_lt_zero_of_ne_zero h)]
        simp
        -- the tens place is equal to n / 10 % 10
        by_cases h : n / 10 = 0
        . {
          exfalso
          rw [Nat.div_eq_zero_iff] at h
          omega
        }
        rw [Nat.digits_def' (by norm_num) (n_lt_zero_of_ne_zero h)]
        simp

        -- simplify the goal
        rw [Nat.div_div_eq_div_mul]
        simp
        -- the hundreds place is equal to n / 100 which is always 2
        have div_100_low := Nat.div_le_div n_ge_200 (show 100 ≤ 100 by norm_num) (by norm_num)
        have div_100_up := Nat.div_lt_div_of_lt_of_dvd (show 100 ∣ 300 by norm_num) n_le_300
        simp at div_100_up
        simp at div_100_low
        have div_100_eq := Nat.eq_of_le_of_lt_succ div_100_low div_100_up
        rw [div_100_eq]
        simp
      . {
        -- prove the set is a superset of {267, 276, 258, 285, 249, 294}
        obtain ⟨a, b, ⟨a_lt_10, b_lt_10, n_digits⟩ ⟩ := exist_a_b
        rw [n_digits] at sum_eq_15
        simp at sum_eq_15
        ring_nf at sum_eq_15
        have n_from_a_b := Nat.ofDigits_digits 10 n
        rw [n_digits] at n_from_a_b
        repeat unfold Nat.ofDigits at n_from_a_b
        ring_nf at n_from_a_b
        simp at n_from_a_b
        rw [<-n_from_a_b]
        -- if a is too small, then b is too big and exceeds 10
        -- a can not exceed 10
        -- values are valid between the bounds
        match a with
        | 0 | 1 | 2 | 3 => {
          repeat exfalso; simp [add_comm] at sum_eq_15; rw [sum_eq_15] at b_lt_10; linarith
        }
        | 4 | 5 | 6 | 7 | 8 | 9 => {
          repeat simp [add_comm] at sum_eq_15; rw [sum_eq_15] at n_digits; rw [sum_eq_15]; simp
        }
        | a + 10 => {
          exfalso
          linarith
        }
      }
    }
    . {
      simp
      -- check each value satisfy the conditions
      repeat intro h; apply Or.by_cases h; intro h; rw [h]; simp
      intro h; rw [h]; simp
    }
  rw [h]
  -- use the fact that the set is finite to
  unfold Set.ncard Set.encard
  simp
