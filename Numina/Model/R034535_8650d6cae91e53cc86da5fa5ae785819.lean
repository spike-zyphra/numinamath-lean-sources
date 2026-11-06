import Mathlib

theorem number_theory_171866 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : Odd (a + b + c + d)) : Even (a * b * c * d) := by
  have h1 : (a + b + c + d) % 2 = 1 := by
    obtain ⟨k, hk⟩ := h
    omega
  by_contra h2
  push_neg at h2
  have h3 : a % 2 = 1 := by
    by_contra h4
    have h4' : a % 2 = 0 := by omega
    have h5 : (a * b * c * d) % 2 = 0 := by
      simp [Nat.mul_mod, h4']
      all_goals omega
    have h6 : Even (a * b * c * d) := by
      exact ⟨(a * b * c * d) / 2, by omega⟩
    tauto
  -- Similarly prove b, c, d are odd
  have h4 : b % 2 = 1 := by
    by_contra h5
    have h5' : b % 2 = 0 := by omega
    have h6 : (a * b * c * d) % 2 = 0 := by
      simp [Nat.mul_mod, h5']
      all_goals omega
    have h7 : Even (a * b * c * d) := by
      exact ⟨(a * b * c * d) / 2, by omega⟩
    tauto
  -- Similarly prove c is odd
  have h5 : c % 2 = 1 := by
    by_contra h6
    have h6' : c % 2 = 0 := by omega
    have h7 : (a * b * c * d) % 2 = 0 := by
      simp [Nat.mul_mod, h6']
      all_goals omega
    have h8 : Even (a * b * c * d) := by
      exact ⟨(a * b * c * d) / 2, by omega⟩
    tauto
  -- Similarly prove d is odd
  have h6 : d % 2 = 1 := by
    by_contra h7
    have h7' : d % 2 = 0 := by omega
    have h8 : (a * b * c * d) % 2 = 0 := by
      simp [Nat.mul_mod, h7']
      all_goals omega
    have h9 : Even (a * b * c * d) := by
      exact ⟨(a * b * c * d) / 2, by omega⟩
    tauto
  -- Now, if a, b, c, d are all odd, their sum is even
  -- This contradicts h1: (a + b + c + d) % 2 = 1
  have h7 : (a + b + c + d) % 2 = 0 := by
    omega
  omega