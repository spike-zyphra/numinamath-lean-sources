import Mathlib

theorem number_theory_187097 :
    IsLeast {x : ℤ | ∃ m n : ℕ, x = |(2015 * m^5 : ℤ) - (2014 * n^4)|} 0 := by
  constructor
  · -- Show 0 is in the set
    use 0
    use 0
    norm_num
  · -- Show no value less than 0 is in the set
    intro x hx
    rcases hx with ⟨m, n, hxn⟩
    have h1 : |(2015 * m^5 : ℤ) - (2014 * n^4)| ≥ 0 := by
      apply abs_nonneg
    linarith