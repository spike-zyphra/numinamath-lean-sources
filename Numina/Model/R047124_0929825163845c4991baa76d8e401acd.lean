import Mathlib

theorem number_theory_318981 (x : ℕ) (hx : 0 < x) (h : ∃ n, n^3 = 2011 - x) :
    x ≥ 283 := by
  rcases h with ⟨n, hn⟩
  by_contra h1
  push_neg at h1
  have h2 : x ≤ 282 := by
    omega
  have h3 : 2011 - x ≥ 1729 := by
    omega
  have h4 : n ^ 3 ≥ 1729 := by 
    omega
  have h5 : n ≥ 13 := by
    by_contra h6
    push_neg at h6
    have h6' : n ≤ 12 := by
      omega
    have h7 : n ^ 3 ≤ 1728 := by
      have h8 : n ≤ 12 := by
        omega
      have h9 : n ^ 3 ≤ (12: ℕ) ^3 := by
        have h10 : n ≤ (12: ℕ) := by omega
        exact Nat.pow_le_pow_of_le_left h10 3
      norm_num at h9 ⊢
      omega
    omega
  have h6 : n ^ 3 ≥ 2197 := by
    have h10 : n ≥ 13 := by
      omega
    have h11 : n ^ 3 ≥ (13: ℕ) ^3 := by
      have h13 : n ≥ (13: ℕ) := by omega
      exact Nat.pow_le_pow_of_le_left h13 3
    norm_num at h11 ⊢
    omega
  have h7 : 2011 - x ≤ 2010 := by
    omega
  omega