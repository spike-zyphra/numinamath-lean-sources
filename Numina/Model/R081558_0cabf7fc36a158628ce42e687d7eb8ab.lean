import Mathlib

theorem algebra_600034 {a b c d : ℤ} (h : ∀ x : ℤ, 5 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by 
  have eq1 := h 0 
  have eq2 := h 1 
  have eq3 := h 2 
  have eq4 := h 3 
  have eq5 := h 4 
  -- Substitute x=0: gives 5 | d
  -- Substitute x=1: gives 5 | a + b + c + d
  -- Substitute x=2: gives 5 | 8*a + 4*b + 2*c + d
  -- Substitute x=3: gives 5 | 27*a + 9*b + 3*c + d
  -- Substitute x=4: gives 5 | 64*a + 16*b + 4*c + d 
  have h5dvd : 5 ∣ d := by 
    omega 
  -- Use above equations to derive divisibility
  -- We need to solve a system of congruences in modular arithmetic
  have h5a : 5 ∣ a := by 
    -- Use simp on the elements of h
    -- Let simp simplify expressions of coefficients mod 5
    have h₁ := h 0
    have h₂ := h 1
    have h₃ := h 2
    have h₄ := h 3
    have h₅ := h 4
    norm_num at h₁ h₂ h₃ h₄ h₅
    -- Let omega handle system of linear equations
    omega 
  have h5b : 5 ∣ b := by 
    -- Use simp on the elements of h
    -- Let simp simplify expressions of coefficients mod 5
    have h₁ := h 0
    have h₂ := h 1
    have h₃ := h 2
    have h₄ := h 3
    have h₅ := h 4
    norm_num at h₁ h₂ h₃ h₄ h₅
    -- Let omega handle system of linear equations
    omega 
  have h5c : 5 ∣ c := by 
    -- Use simp on the elements of h
    -- Let simp simplify expressions of coefficients mod 5
    have h₁ := h 0
    have h₂ := h 1
    have h₃ := h 2
    have h₄ := h 3
    have h₅ := h 4
    norm_num at h₁ h₂ h₃ h₄ h₅
    -- Let omega handle system of linear equations
    omega 
  -- As shown above, 5 divides a, b, c, and d
  -- Now prove these implications
  constructor 
  · exact h5a 
  constructor 
  · exact h5b 
  constructor 
  · exact h5c 
  · exact h5dvd