import Mathlib

theorem number_theory_15682 :
  IsGreatest {n : ℤ | 0 < n ∧ ∀ a d : ℤ, 0 < a → 0 < d → n ∣ ∑ i ∈ Finset.range 10, (a + d * i)} 5 := by
  constructor
  · -- Show that 5 is in the set
    constructor
    · norm_num
    · intro a d ha hd
      have h1 : ∑ i in Finset.range 10, (a + d * i) = 10 * a + 45 * d := by
        norm_num [Finset.sum_range_succ]
        <;> ring
      rw [h1]
      use 2 * a + 9 * d
      all_goals ring
  · -- Show that 5 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    have h1 := h 1 1 (by norm_num) (by norm_num)
    have h1' : n ∣ 55 := by
      norm_num [Finset.sum_range_succ] at h1 ⊢
      all_goals try tauto
    -- Second specific example to get another divisibility condition
    have h2 := h 1 2 (by norm_num) (by norm_num)
    have h2' : n ∣ 100 := by
      norm_num [Finset.sum_range_succ] at h2 ⊢
      all_goals try tauto
    -- From n divides 55 and 100, n divides gcd(55, 100) = 5
    have h3 : n ∣ 5 := by
      exact Int.dvd_gcd h1' h2'
    -- If n divides 5 and is positive, then n ≤ 5
    have h4 : n ≤ 5 := by
      exact Int.le_of_dvd (by norm_num) h3
    linarith