import Mathlib

/- Find the 6 -digit number beginning and ending in the digit 2 that is the product of three consecutive even integers.-/
theorem number_theory_610843 :
    {m : ℕ | ∃ a₂ a₃ a₄ a₅ n : ℕ, a₂ ≤ 9 ∧ a₃ ≤ 9 ∧ a₄ ≤ 9 ∧ a₅ ≤ 9 ∧ Even n ∧ m = n * (n + 2) * (n + 4) ∧ m = 200000 + a₂ * 10000 + a₃ * 1000 + a₄ * 100 + a₅ * 10 + 2} = {287232} := by
  -- First simplify the goal into two parts.
  ext m
  apply Iff.intro
  . -- First show that the condition implies that m = 287232.
    simp
    intro a₂ ha₂ a₃ ha₃ a₄ ha₄ a₅ ha₅ n hn h₀ h₁
    -- Show that n must ends with digit 4.
    have h₂ : n % 10 = 4 := by
      rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hn
      have h₂ : n % 10 = 0 ∨ n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 := by
        omega
      -- Consider m = n (n + 2) (n + 4) % 10 to show that only the case n % 10 = 4 is possible.
      replace h₀ := congr_arg (· % 10) h₀
      simp at h₀
      rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂)
      all_goals
        simp [Nat.mul_mod, Nat.add_mod, h₂] at h₀
        omega
    -- Show that n + 2 > 58.
    have h₃ : (n + 2) ^ 3 > 58 ^ 3 := by
      calc
        (n + 2) ^ 3 ≥ (n + 2) ^ 3 - 4 * (n + 2) := by omega
        _ = n * (n + 2) * (n + 4) := by
          apply Nat.sub_eq_of_eq_add
          ring
        _ > 58 ^ 3 := by
          -- Since n = 2XXXXX, n > 58³ = 195112.
          rw [<-h₀]
          omega
    rw [gt_iff_lt, Nat.pow_lt_pow_iff_left (by norm_num)] at h₃
    -- Show that n > 60.
    have h₄ : n > 60 := by
      omega
    -- Show that n < 67.
    have h₄ : n ^ 3 < 67 ^ 3 := by
      calc
        n ^ 3 ≤ n * (n + 2) * (n + 4) := by
          ring_nf
          omega
        _ < 67 ^ 3 := by
          -- Since n = 2XXXXX, n < 67³ = 300763.
          rw [<-h₀]
          omega
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h₄
    -- Show that n = 64.
    have h₅ : n = 64 := by
      omega
    -- We get the result.
    simp [h₀, h₅]
  . -- Now verify that m = 287232 satisfies the condition.
    intro h
    simp at h
    simp [h]
    use 8, by norm_num, 7, by norm_num, 2, by norm_num, 3, by norm_num, 64
    norm_num
    -- Verify that 64 is even.
    use 32
