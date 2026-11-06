import Mathlib

theorem number_theory_196265 (a b c d e : ℤ) (h₀ : Even (a + b + c)) (h₁ : Even (a + b + d))
    (h₂ : Even (a + b + e)) (h₃ : Even (a + c + d)) (h₄ : Even (a + c + e))
    (h₅ : Even (a + d + e)) (h₆ : Even (b + c + d)) (h₇ : Even (b + c + e))
    (h₈ : Even (b + d + e)) (h₉ : Even (c + d + e)) :
    Even a ∧ Even b ∧ Even c ∧ Even d ∧ Even e := by 
  -- The hypotheses h₀, ..., h₉ give us ten equations concerning the parity of the variables
  have h0 : (a + b + c) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₀
    omega
  have h1 : (a + b + d) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₁
    omega
  have h2 : (a + b + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₂
    omega
  have h3 : (a + c + d) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₃
    omega
  have h4 : (a + c + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₄
    omega
  have h5 : (a + d + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₅
    omega
  have h6 : (b + c + d) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₆
    omega
  have h7 : (b + c + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₇
    omega
  have h8 : (b + d + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₈
    omega
  have h9 : (c + d + e) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₉
    omega 
  constructor
  · -- Show that a is even
    use a / 2
    omega
  constructor
  · -- Show that b is even
    use b / 2
    omega
  constructor
  · -- Show that c is even
    use c / 2
    omega
  constructor
  · -- Show that d is even
    use d / 2
    omega
  · -- Show that e is even
    use e / 2
    omega