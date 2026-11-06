import Mathlib

theorem algebra_289282 {x y n m : ℤ} (h₀ : x + 2 * y = n) (h₁ : 3 * x - y = m)
    (h₂ : Odd n) (h₃ : Odd m) :
    Odd x ∧ Even y := by
        have h4 : x % 2 = 1 := by 
            obtain ⟨k, hk⟩ := h₂
            omega
        have h5 : y % 2 = 0 := by 
            obtain ⟨k, hk⟩ := h₂
            obtain ⟨j, hj⟩ := h₃
            omega
        constructor
        · -- x is odd
          exact ⟨(x - 1) / 2, by omega⟩
        · -- y is even
          exact ⟨y / 2, by omega⟩