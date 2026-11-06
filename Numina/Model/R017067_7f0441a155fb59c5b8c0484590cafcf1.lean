import Mathlib

theorem number_theory_128084 (a : ℕ → ℕ) (ha : ∀ n, a n = 7 * n + 1) :
    IsGreatest {x | ∃ n, x = a n ∧ x ∈ Finset.Icc 100 999} 995 := by
  constructor
  · -- Show 995 is in the set
    use 142
    constructor
    · -- Show that 995 = a 142
      rw [ha 142]
      all_goals norm_num
    · -- Show 995 is in the interval [100, 999]
      norm_num [Finset.mem_Icc]
  · -- Show any element in the set is ≤ 995
    intro x hx
    rcases hx with ⟨n, hx0, hx1⟩
    have hx2 : x = 7 * n + 1 := by
      rw [hx0]
      rw [ha n]
    have hx3 : x ∈ Finset.Icc 100 999 := hx1
    rw [Finset.mem_Icc] at hx3
    rw [show x = 7 * n + 1 by omega] at hx3
    have h2 : 7 * n + 1 ≤ 999 := by
      omega -- This is equivalent to the second part of hx3
    have h3 : n ≤ 142 := by
      omega
    have h4 : 7 * n + 1 ≤ 995 := by
      omega
    omega -- This will use hx2 : x = 7 * n + 1 with h4