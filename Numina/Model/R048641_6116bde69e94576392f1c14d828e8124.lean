import Mathlib

theorem number_theory_239154 : (Nat.floor (10^2006 * (469 / 1998 : ℝ)) % 10) = 3 := by
  have h1 : Nat.floor (10^2006 * (469 / 1998 : ℝ)) = (10^2006 * 469) / 1998 := by
    norm_num [Nat.floor_eq_iff]
    all_goals omega
  calc
    Nat.floor (10^2006 * (469 / 1998 : ℝ)) % 10 
        = ((10^2006 * 469) / 1998) % 10 := by rw [h1]
    _ = 3 := by
      norm_num