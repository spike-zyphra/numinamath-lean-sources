import Mathlib

theorem algebra_94263 : IsLeast {M : ℕ | ∃ (a b c d e :ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
a + b + c + d + e = 2010 ∧ M = (a+b) ⊔ (b+c) ⊔ (c+d) ⊔ (d+e)} 671 := by
  constructor
  · -- Show 671 is in the set
    use 668, 3, 668, 3, 668
    all_goals norm_num
  · -- Show 671 is minimal
    intro M h
    rcases h with ⟨a, b, c, d, e, ha, hb, hc, hd, he, hsum, hM⟩
    by_contra h
    push_neg at h
    have h1 : (a + b) < 671 := by
      omega
    have h2 : (b + c) < 671 := by
      omega
    have h3 : (c + d) < 671 := by
      omega
    have h4 : (d + e) < 671 := by 
      omega
    omega