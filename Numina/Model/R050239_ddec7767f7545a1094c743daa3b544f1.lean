import Mathlib

theorem number_theory_245527 : IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ n % 7 = 1} 995 := by
  constructor
  · -- Show that 995 is in the set
    constructor
    · -- Show that 995 is a three-digit number
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that 995 gives a remainder of 1 when divided by 7
      norm_num
  · -- Show that 995 is the greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1, h2⟩
    -- Now, we need to show that n ≤ 995
    -- Since n % 7 = 1 and n ≤ 999
    -- We can prove that n ≤ 995
    omega