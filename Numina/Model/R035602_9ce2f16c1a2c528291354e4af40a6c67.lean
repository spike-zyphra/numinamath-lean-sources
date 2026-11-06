import Mathlib

theorem algebra_1473 {x y p q : ℤ} (h₀ : Even p) (h₁ : Odd q)
    (h₂ : x - 1992 * y = p) (h₃ : 1993 * x + 3 * y = q) :
    Even x ∧ Odd y := by 
  have h4 : x % 2 = 0 := by
    have h5 : p % 2 = 0 := by 
      obtain ⟨k, hk⟩ := h₀
      omega 
    omega 
  have h6 : y % 2 = 1 := by 
    have h7 : q % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₁
      omega 
    omega 
  constructor 
  · -- x is even
    have : Even x := by 
      refine' ⟨x / 2, by omega⟩ 
    exact this 
  · -- y is odd
    have : Odd y := by 
      refine' ⟨y / 2, by omega⟩ 
    exact this