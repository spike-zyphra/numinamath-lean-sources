import Mathlib

/- Let $n$ be an integer and

$$
m=(n-1001)(n-2001)(n-2002)(n-3001)(n-3002)(n-3003) .
$$

Given that $m$ is positive, find the minimum number of digits of $m$.-/
theorem algebra_610354 :
    IsLeast {x | ∃ m : ℕ, ∃ n : ℤ, 0 < m ∧ m = (n - 1001) * (n - 2001) * (n - 2002) * (n - 3001) * (n - 3002) * (n - 3003) ∧ x = (Nat.digits 10 m).length} 11 := by
  constructor
  . -- Show that 11 is attainable.
    use 12078162108, 3004
    norm_num
  . -- Show that 11 is the minimum possible number of digits of m.
    simp [lowerBounds]
    intro x m hm n hn hx
    -- It suffices to show that 12078162108 ≤ m.
    suffices 12078162108 ≤ m by
      have h₀ := Nat.digits_len 10 m (by norm_num) (by omega)
      rw [hx, h₀]
      simp
      nth_rw 1 [show 10 = Nat.log 10 (10 ^ 10) by rw [Nat.log_pow (by norm_num)]]
      apply Nat.log_mono_right
      linarith
    -- Consider cases for n.
    by_cases h₀ : n < 1001
    . -- Case n < 1001: m is positive but too large.
      zify
      calc
        (12078162108 : ℤ) ≤ 1 * 1001 * 1002 * 2001 * 2002 * 2003 := by norm_num
        _ ≤ (1001 - n) * (2001 - n) * (2002 - n) * (3001 - n) * (3002 - n) * (3003 - n) := by
          repeat
            first | apply mul_le_mul | apply mul_nonneg | omega
        _ = m := by
          linarith
    . by_cases h₁ : n = 1001
      . -- Case n = 1001 : m = 0.
        norm_num [h₁] at hn
        linarith
      . by_cases h₂ : n < 2001
        . -- Case 1001 < n < 2001 : m is negative.
          have hm' : m < 0 := by
            zify
            rw [hn]
            apply mul_neg_of_pos_of_neg
            apply mul_pos_of_neg_of_neg
            apply mul_neg_of_pos_of_neg
            apply mul_pos_of_neg_of_neg
            apply mul_neg_of_pos_of_neg
            all_goals
              omega
          linarith
        . by_cases h₃ : n = 2001
          . -- Case n = 2001 : m = 0.
            norm_num [h₃] at hn
            linarith
          . by_cases h₄ : n = 2002
            . -- Case n = 2002 : m = 0.
              norm_num [h₄] at hn
              linarith
            . by_cases h₅ : n < 3001
              . -- Case 2002 < n < 3001 : m is negative.
                have hm' : m < 0 := by
                  zify
                  rw [hn]
                  apply mul_neg_of_pos_of_neg
                  apply mul_pos_of_neg_of_neg
                  apply mul_neg_of_pos_of_neg
                  apply mul_pos
                  apply mul_pos
                  all_goals
                    omega
                linarith
              . by_cases h₆ : n = 3001
                . -- Case n = 3001 : m = 0.
                  norm_num [h₆] at hn
                  linarith
                . by_cases h₇ : n = 3002
                  . -- Case n = 3002 : m = 0.
                    norm_num [h₇] at hn
                    linarith
                  . by_cases h₈ : n = 3003
                    . -- Case n = 3003 : m = 0.
                      norm_num [h₈] at hn
                      linarith
                    . -- Case n > 3003 : m is positive and the minimum is attained when n = 3004.
                      zify
                      calc
                        (12078162108 : ℤ) ≤ 2003 * 1003 * 1002 * 3 * 2 * 1 := by norm_num
                        _ ≤ (n - 1001) * (n - 2001) * (n - 2002) * (n - 3001) * (n - 3002) * (n - 3003) := by
                          repeat
                            first | apply mul_le_mul | apply mul_nonneg | omega
                        _ = m := by
                          linarith
