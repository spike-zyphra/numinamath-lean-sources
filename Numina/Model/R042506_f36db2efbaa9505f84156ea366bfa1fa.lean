import Mathlib

theorem number_theory_61295 (m : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ (5 ^ n) % 10 ^ (Nat.digits 10 (5 ^ m)).length = 5 ^ m := by 
  use m 
  constructor 
  · -- Show that n is positive 
    exact hm
  · -- Show that $5^n \% 10^{k} = 5^m$ where k is the number of digits in $5^m$
    have h1 : (5 ^ m) % 10 ^ (Nat.digits 10 (5 ^ m)).length = 5 ^ m := by 
      have h2 : 5 ^ m < 10 ^ (Nat.digits 10 (5 ^ m)).length := by 
        -- Show that $5^m < 10^l$ where $l$ is length of digits of $5^m$ in base 10
        have h3 : (Nat.digits 10 (5 ^ m)).length = Nat.log 10 (5 ^ m) + 1 := by 
          rw [Nat.digits_len]
          all_goals 
            -- Show positivity and the base is valid
            have h5_pos : 5 ^ m > 0 := by 
              apply Nat.pow_pos 
              norm_num 
            have h10_pos : (10 : ℕ) > 1 := by norm_num
            -- Prove by properties of Nat.digits and Nat.log 
            all_goals 
              have h5_ge_1 : (5 : ℕ) ^ m ≥ 1 := by 
                have h1_pos : m > 0 := hm
                have h5_pos' : (5 : ℕ) ^ m > 0 := by 
                  apply Nat.pow_pos 
                  norm_num 
                have h5_ge_1 : (5 : ℕ) ^ m ≥ 1 := by 
                  apply Nat.one_le_pow 
                  norm_num 
                  all_goals linarith [hm] 
                linarith [h5_pos'] 
              nlinarith 
        rw [h3] 
        -- Need to show inequality using logarithm 
        -- Show 5^m < 10^(Nat.log 10 (5^m) + 1)
        have h3' : 5 ^ m < 10 ^ (Nat.log 10 (5 ^ m) + 1) := by 
          have h8 : Nat.log 10 (5 ^ m) = Nat.log 10 (5 ^ m) := rfl 
          -- Use natural logarithm properties 
          -- Note this is essentially using the definition of logarithm
          have h9 : 5 ^ m < 10 ^ (Nat.log 10 (5 ^ m) + 1) := by 
            have h5_pos : 5 ^ m > 0 := by 
              apply Nat.pow_pos 
              norm_num 
            have h5_ge_1 : (5 : ℕ) ^ m ≥ 1 := by 
              have h1_pos : m > 0 := hm
              have h5_pos' : (5 : ℕ) ^ m > 0 := by 
                apply Nat.pow_pos 
                norm_num 
              have h5_ge_1 : (5 : ℕ) ^ m ≥ 1 := by 
                apply Nat.one_le_pow 
                norm_num 
                all_goals linarith [hm] 
              linarith [h5_pos'] 
            have h5_lt : (5 : ℕ) ^ m < 10 ^ (Nat.log 10 (5 ^ m) + 1) := by 
              have h6 : Nat.log 10 (5 ^ m) = Nat.log 10 (5 ^ m) := rfl 
              apply Nat.lt_pow_of_log_lt 
              all_goals 
                -- Use inner positivity of 5^m
                have h5_pos' : 5 ^ m > 0 := by 
                  apply Nat.pow_pos 
                  norm_num 
                have h5_pos'' : (5 : ℕ) ^ m > 0 := by 
                  nlinarith [show 5 ^ m > 0 by apply Nat.pow_pos; norm_num] 
                -- Continue with property applications
                all_goals 
                  nlinarith 
            linarith [h5_lt] 
          linarith 
        linarith 
      apply Nat.mod_eq_of_lt 
      linarith 
    exact_mod_cast h1