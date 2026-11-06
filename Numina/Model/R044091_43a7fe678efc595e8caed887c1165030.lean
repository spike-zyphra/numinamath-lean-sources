import Mathlib

open Nat Finset

theorem number_theory_3995 :
IsLeast { x | ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
∧ a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
d = a^2 * b^2 - 49 * c^2 ∧
x = a + b + c } 10 := by 
  constructor
  · -- Show 10 is achievable 
    use 3, 5, 2, 29
    all_goals norm_num
  · -- Show there's no smaller value
    intro x hx 
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h1, h2, h3, h4, h5, h6, hap, hbp, hcp, hdp, heq, hx⟩
    by_contra h
    push_neg at h
    have h10 : a + b + c < 10 := by linarith [h, hx]
    have h100 : a ≤ 7 := by
      omega
    have h101 : b ≤ 7 := by
      omega
    have h102 : c ≤ 7 := by
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c 
      <;> norm_num at heq hap hbp hcp hdp 
      <;> omega