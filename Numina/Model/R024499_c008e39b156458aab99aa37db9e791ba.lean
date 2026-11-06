import Mathlib

theorem number_theory_211201 {n : ℕ} (hn : n % 2021 = (n % 2020) + 800) :
    IsLeast {n | n % 2021 = (n % 2020) + 800} 2466420 := by
  constructor
  · -- Show 2466420 is in the set
    show 2466420 % 2021 = (2466420 % 2020) + 800
    all_goals norm_num
  · -- Show that 2466420 is the smallest
    intro n hn
    have h : n % 2021 = (n % 2020) + 800 := hn
    omega