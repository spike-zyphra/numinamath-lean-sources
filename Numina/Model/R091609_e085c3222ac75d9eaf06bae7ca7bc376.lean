import Mathlib

theorem algebra_136190 (n : ℤ) :
    (∏ i ∈ Finset.range 1008, (n - 2 * i - 1)) = (∏ i ∈ Finset.range 1008, (n + 2 * i)) ↔
    False := by
  constructor
  · -- Assume equality and derive False
    intro h
    have h₁ : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by 
      omega
    rcases h₁ with (h₁ | h₁)
    · -- Case where n is even
      have h₂ : (∏ i ∈ Finset.range 1008, (n + 2 * i)) % 2 = 0 := by
        have h3 : ∀ i : ℕ, (n + 2 * (i:ℤ)) % 2 = 0 := by 
          intro i
          have h4 : ((2 * ((i : ℤ))): ℤ) % 2 = 0 := by 
            simp [Int.mul_emod, Int.add_emod]
          omega
        simp [Finset.prod_int_mod, h3]
      have h₃ : (∏ i ∈ Finset.range 1008, (n - 2 * i - 1)) % 2 = 1 := by
        have h4 : ∀ i : ℕ, ((n - 2 * (i : ℤ) - 1) : ℤ) % 2 = 1 := by
          intro i
          have h5 : ((2 * ((i : ℤ))): ℤ) % 2 = 0 := by 
            simp [Int.mul_emod, Int.add_emod]
          omega
        simp [Finset.prod_int_mod, h4]
      have h' : (∏ i ∈ Finset.range 1008, (n - 2 * i - 1)) % 2 = (∏ i ∈ Finset.range 1008, (n + 2 * i)) % 2 := by 
        omega
      omega 
    · -- Case where n is odd
      have h₂ : (∏ i ∈ Finset.range 1008, (n + 2 * i)) % 2 = 1 := by
        have h4 : ∀ i : ℕ, ((n + 2 * (i : ℤ)) : ℤ) % 2 = 1 := by
          intro i
          have h5 : ((2 * ((i : ℤ))): ℤ) % 2 = 0 := by 
            simp [Int.mul_emod, Int.add_emod]
          omega
        simp [Finset.prod_int_mod, h4]
      have h₃ : (∏ i ∈ Finset.range 1008, (n - 2 * i - 1)) % 2 = 0 := by
        have h5 : ∀ i : ℕ, ((n - 2 * (i : ℤ) - 1) : ℤ) % 2 = 0 := by
          intro i
          have h6 : ((2 * ((i : ℤ))): ℤ) % 2 = 0 := by 
            simp [Int.mul_emod, Int.add_emod]
          omega
        simp [Finset.prod_int_mod, h5]
      have h' : (∏ i ∈ Finset.range 1008, (n - 2 * i - 1)) % 2 = (∏ i ∈ Finset.range 1008, (n + 2 * i)) % 2 := by 
        omega
      omega
  · -- Backward direction: False implies anything
    intro h
    cases h