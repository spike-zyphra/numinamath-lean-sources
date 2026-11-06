import Mathlib

/- 1. If any prime number is divided by thirty, the remainder will be 1 or a prime number. Prove it. -/
theorem number_theory_266978 (p : ℕ) (hp : p.Prime) :
    p % 30 = 1 ∨ (p % 30).Prime := by
    -- do casework on mod values
  mod_cases h : p % 30
  -- those remainders that are prime are handled easily
  any_goals (
    rw [h]
    norm_num
  )

  all_goals (
    -- otherwise remainders divisible by 2 means 2 ∣ p then p = 2, but that won't match with remainder in case
    if h_div_2 : p % 30 % 2 = 0 then (
      have : p % 2 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 30 by norm_num)]; assumption
      have : 2 = p := by
        apply Or.resolve_left (hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero this))
        norm_num
      rw [← this] at h
      simp [Nat.ModEq] at h
    )
    -- remainders divisible by 3 means 3 ∣ p then p = 3, but that won't match with remainder in case
    else if h_div_3 : p % 30 % 3 = 0 then (
      have : p % 3 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 3 ∣ 30 by norm_num)]; assumption
      have : 3 = p := by
        apply Or.resolve_left (hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero this))
        norm_num
      rw [← this] at h
      simp [Nat.ModEq] at h
    )
    -- otherwise remainders divisible by 5 means 5 ∣ p then p = 5, but that won't match with remainder in case
    else if h_div_5 : p % 30 % 5 = 0 then (
      have : p % 5 = 0 := by rw [← Nat.mod_mod_of_dvd p (show 5 ∣ 30 by norm_num)]; assumption
      have : 5 = p := by
        apply Or.resolve_left (hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero this))
        norm_num
      rw [← this] at h
      simp [Nat.ModEq] at h
    )
    else (
      -- above 3 covers all cases, so pluggin in p % 30 at the remainder equations will create contradiction
      rw [h] at h_div_2 h_div_3 h_div_5
      norm_num at h_div_2 h_div_3 h_div_5
    )
  )