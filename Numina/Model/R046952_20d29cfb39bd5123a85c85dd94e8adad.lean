import Mathlib

theorem number_theory_348 :
    IsLeast {x | ∃ a b c d e : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ a + b + c + d + e = 15 ∧ x = a * b + b * c + c * d + d * e + e * a} 37 := by 
  constructor
  · -- Show that 37 is in the set.
    use 1, 5, 2, 3, 4
    all_goals norm_num
  · -- Show that 37 is the minimum value in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, e, ha, hb, hc, hd, he, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde, hsum, hx⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 5 := by
      omega
    have h2 : b ≤ 5 := by
      omega
    have h3 : c ≤ 5 := by
      omega
    have h4 : d ≤ 5 := by
      omega
    have h5 : e ≤ 5 := by
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega