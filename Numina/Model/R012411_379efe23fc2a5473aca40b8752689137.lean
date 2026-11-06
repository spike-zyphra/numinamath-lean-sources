import Mathlib

theorem algebra_141376 (p q : ℕ) :
    (∃ h : ℤ, p^3 - q^3 = 2 * h) ↔ Even (p + q) := by 
  constructor 
  · -- Assume there exists an integer h such that p^3 - q^3 = 2 * h, prove that p + q is even.
    rintro ⟨h, h_eq⟩
    have h1 : (p : ℤ) % 2 = 0 ∨ (p : ℤ) % 2 = 1 := by 
      omega
    have h2 : (q : ℤ) % 2 = 0 ∨ (q : ℤ) % 2 = 1 := by 
      omega
    have h3 : (p : ℤ) ^ 3 % 2 = (p : ℤ) % 2 := by
      rcases h1 with (h1 | h1)
      ·
        simp [Int.add_emod, Int.mul_emod, pow_succ, h1]
      ·
        simp [Int.add_emod, Int.mul_emod, pow_succ, h1]
    have h4 : (q : ℤ) ^ 3 % 2 = (q : ℤ) % 2 := by
      rcases h2 with (h2 | h2)
      ·
        simp [Int.add_emod, Int.mul_emod, pow_succ, h2]
      ·
        simp [Int.add_emod, Int.mul_emod, pow_succ, h2]
    have h5 : (p : ℤ) % 2 = (q : ℤ) % 2 := by 
      omega 
    have h5' : (p + q) % 2 = 0 := by 
      omega 
    have h6 : Even (p + q) := by 
      refine' ⟨(p + q) / 2, by omega⟩
    exact h6 
  · -- Assume that p + q is even, prove that there exists an integer h such that p^3 - q^3 = 2 * h.
    rintro ⟨k, hk⟩ 
    have h1 : (p : ℤ) % 2 = (q : ℤ) % 2 := by 
      have h3 : p + q = 2 * k := by 
        norm_num at hk ⊢
        omega 
      omega 
    have h2 : (p^3 : ℤ) % 2 = (q^3 : ℤ) % 2 := by 
      have hp1 : (p^3 : ℤ) % 2 = (p : ℤ) % 2 := by
        have h2 : (p : ℤ) % 2 = 0 ∨ (p : ℤ) % 2 = 1 := by 
          omega
        rcases h2 with (h2 | h2)
        · 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h2]
        · 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h2]
      have hq1 : (q^3 : ℤ) % 2 = (q : ℤ) % 2 := by
        have h3 : (q : ℤ) % 2 = 0 ∨ (q : ℤ) % 2 = 1 := by 
          omega
        rcases h3 with (h3 | h3)
        · 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h3]
        · 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h3]
      have h6 : (p : ℤ) % 2 = (q : ℤ) % 2 := h1 
      omega 
    refine' ⟨(p^3 - q^3) / 2, by omega⟩