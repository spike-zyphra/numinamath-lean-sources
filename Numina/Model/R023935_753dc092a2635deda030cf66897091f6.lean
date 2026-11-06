import Mathlib

theorem number_theory_203156 (a b c d e f g : ℕ) :
    Even (a + b) ∨ Even (b + c) ∨ Even (c + d) ∨ Even (d + e) ∨
    Even (e + f) ∨ Even (f + g) ∨ Even (g + a) := by
  by_contra h
  have h1 : ¬Even (a + b) := by
    tauto
  have h2 : ¬Even (b + c) := by
    tauto
  have h3 : ¬Even (c + d) := by
    tauto
  have h4 : ¬Even (d + e) := by
    tauto
  have h5 : ¬Even (e + f) := by
    tauto
  have h6 : ¬Even (f + g) := by
    tauto
  have h7 : ¬Even (g + a) := by
    tauto
  have h8 : (a + b) % 2 = 1 := by 
    have h8 : ¬Even (a + b) := h1
    have h9 : (a + b) % 2 = 1 := by
      by_cases h10 : (a + b) % 2 = 0 
      · -- Assume (a + b) % 2 = 0, that is even 
        have h11 : Even (a + b) := by
          refine' ⟨(a + b) / 2, by omega⟩
        tauto 
      · -- (a + b) % 2 ≠ 0, so since it's Nat, it's 1.
        omega
    exact h9
  have h9 : (b + c) % 2 = 1 := by 
    have h9 : ¬Even (b + c) := h2
    have h10 : (b + c) % 2 = 1 := by 
      by_cases h11 : (b + c) % 2 = 0 
      · -- Assume (b + c) % 2 = 0 
        have h12 : Even (b + c) := by
          refine' ⟨(b + c) / 2, by omega⟩
        tauto 
      · -- (b + c) % 2 ≠ 0 
        omega 
    exact h10
  have h10 : (c + d) % 2 = 1 := by 
    have h10 : ¬Even (c + d) := h3
    have h11 : (c + d) % 2 = 1 := by 
      by_cases h12 : (c + d) % 2 = 0 
      · -- Assume (c + d) % 2 = 0 
        have h13 : Even (c + d) := by
          refine' ⟨(c + d) / 2, by omega⟩
        tauto 
      · -- (c + d) % 2 ≠ 0 
        omega 
    exact h11
  have h11 : (d + e) % 2 = 1 := by 
    have h11 : ¬Even (d + e) := h4
    have h12 : (d + e) % 2 = 1 := by 
      by_cases h13 : (d + e) % 2 = 0 
      · -- Assume (d + e) % 2 = 0 
        have h14 : Even (d + e) := by
          refine' ⟨(d + e) / 2, by omega⟩
        tauto 
      · -- (d + e) % 2 ≠ 0 
        omega 
    exact h12
  have h12 : (e + f) % 2 = 1 := by 
    have h12 : ¬Even (e + f) := h5
    have h13 : (e + f) % 2 = 1 := by 
      by_cases h14 : (e + f) % 2 = 0 
      · -- Assume (e + f) % 2 = 0 
        have h15 : Even (e + f) := by
          refine' ⟨(e + f) / 2, by omega⟩
        tauto 
      · -- (e + f) % 2 ≠ 0 
        omega 
    exact h13
  have h13 : (f + g) % 2 = 1 := by 
    have h13 : ¬Even (f + g) := h6
    have h14 : (f + g) % 2 = 1 := by 
      by_cases h15 : (f + g) % 2 = 0 
      · -- Assume (f + g) % 2 = 0 
        have h16 : Even (f + g) := by
          refine' ⟨(f + g) / 2, by omega⟩
        tauto 
      · -- (f + g) % 2 ≠ 0 
        omega 
    exact h14
  have h14 : (g + a) % 2 = 1 := by 
    have h14 : ¬Even (g + a) := h7
    have h15 : (g + a) % 2 = 1 := by 
      by_cases h16 : (g + a) % 2 = 0 
      · -- Assume (g + a) % 2 = 0 
        have h17 : Even (g + a) := by
          refine' ⟨(g + a) / 2, by omega⟩
        tauto 
      · -- (g + a) % 2 ≠ 0 
        omega 
    exact h15
  omega