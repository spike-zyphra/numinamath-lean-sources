import Mathlib

/- Example 6 Try to prove: For any prime number greater than 5, the remainder when its square is divided by 30 can only be 1 or 19. -/
theorem number_theory_283008 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p) :
    p^2 ≡ 1 [ZMOD 30] ∨ p^2 ≡ 19 [ZMOD 30] := by
  -- change to mod version and nat version
  change p^2 % 30 = (1 : ℤ) % 30 ∨ p^2 % 30 = (19 : ℤ) % 30
  norm_cast
  -- first prove p % 30 is from 1, 7, 11, 13, 17, 19, 23, 29
  have : p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨ p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
    -- do casework on mod values
    mod_cases h : p % 30
    any_goals (
      rw [h]
      norm_num
    )
    -- for remainder being divisible by 2, 3, 5, we can prove they must be p's divisor, but then p > 5 creates contradiction
    all_goals (
      if h_div_2 : p % 30 % 2 = 0 then (
        have : p % 2 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 30 by norm_num)]; assumption
        obtain h | h := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero this) <;> linarith
      )
      else if h_div_3 : p % 30 % 3 = 0 then (
        have : p % 3 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 3 ∣ 30 by norm_num)]; assumption
        obtain h | h := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero this) <;> linarith
      )
      else if h_div_5 : p % 30 % 5 = 0 then (
        have : p % 5 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 5 ∣ 30 by norm_num)]; assumption
        obtain h | h := hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero this) <;> linarith
      )
      else (
        rw [h] at h_div_2 h_div_3 h_div_5
        norm_num at h_div_2 h_div_3 h_div_5
      )
    )
  -- now plug in the values for each case and compute
  obtain h | h | h | h | h | h | h | h := this
  all_goals (
    rw [sq, Nat.mul_mod, h]
    norm_num
  )