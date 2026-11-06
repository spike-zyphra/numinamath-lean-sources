import Mathlib

theorem number_theory_73213 :
    IsLeast {x | ∃ n m : ℤ, x = |(n * 364 + m * 715) - 2010|} 5 := by 
  constructor
  · -- First part: show that 5 exists in the set
    use 310, -155
    norm_num [abs]
  · -- Second part: prove that 5 is minimal
    intro x hx
    rcases hx with ⟨n, m, rfl⟩
    by_contra h
    push_neg at h
    have h1 : n * 364 + m * 715 - 2010 ≥ -4 := by
      cases' abs_cases (n * 364 + m * 715 - 2010) with h2 h2
      · -- Case where n * 364 + m * 715 - 2010 ≥ 0
        linarith
      · -- Case where n * 364 + m * 715 - 2010 < 0
        linarith
    have h2 : n * 364 + m * 715 - 2010 ≤ 4 := by
      cases' abs_cases (n * 364 + m * 715 - 2010) with h2 h2
      · -- Case where n * 364 + m * 715 - 2010 ≥ 0
        linarith
      · -- Case where n * 364 + m * 715 - 2010 < 0
        linarith
    have h3 : n * 364 + m * 715 ≥ 2006 := by linarith
    have h4 : n * 364 + m * 715 ≤ 2014 := by linarith
    omega