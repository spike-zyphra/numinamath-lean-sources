import Mathlib

theorem number_theory_301886 (a : ℚ) :
    ⌊a⌋ + ⌊-a⌋ = 0 ∨ ⌊a⌋ + ⌊-a⌋ = -1 := by 
  have h1 : ⌊a⌋ ≤ (a : ℚ) := by 
    exact Int.floor_le a 
  have h2 : (a : ℚ) < (⌊a⌋ + 1 : ℚ) := by 
    exact Int.lt_floor_add_one a 
  have h3 : ⌊-a⌋ ≤ (-a : ℚ) := by 
    exact Int.floor_le (-a)
  have h4 : (-a : ℚ) < (⌊-a⌋ + 1 : ℚ) := by 
    exact Int.lt_floor_add_one (-a)
  have h5 : ⌊a⌋ + ⌊-a⌋ ≤ (0 : ℤ) := by 
    have h6 : (⌊a⌋ : ℚ) + (⌊-a⌋ : ℚ) ≤ (a : ℚ) + (-a : ℚ) := by 
      linarith [h1, h3]
    have h7 : (a : ℚ) + (-a : ℚ) = (0 : ℚ) := by 
      ring
    have h8 : (⌊a⌋ : ℚ) + (⌊-a⌋ : ℚ) ≤ (0 : ℚ) := by 
      linarith [h6, h7]
    have h9 : (⌊a⌋ + ⌊-a⌋ : ℤ) ≤ (0 : ℤ) := by 
      exact_mod_cast h8
    omega
  have h6 : ⌊a⌋ + ⌊-a⌋ > (-2 : ℤ) := by
    have h7 : (⌊a⌋ : ℚ) + (⌊-a⌋ : ℚ) < (⌊a⌋ + 1 : ℚ) + (⌊-a⌋ + 1 : ℚ) := by 
      linarith [h2, h4]
    have h8 : (⌊a⌋ + 1 : ℚ) + (⌊-a⌋ + 1 : ℚ) = (⌊a⌋ + ⌊-a⌋ + 2 : ℚ) := by 
      ring
    have h9 : (⌊a⌋ : ℚ) + (⌊-a⌋ : ℚ) < (⌊a⌋ + ⌊-a⌋ + 2 : ℚ) := by 
      linarith [h7, h8]
    have h10 : (⌊a⌋ + ⌊-a⌋ : ℤ) > (-2 : ℤ) := by 
      by_contra h
      push_neg at h
      have h11 : (⌊a⌋ + ⌊-a⌋ : ℤ) ≤ (-2 : ℤ) := by 
        omega
      have h12 : (⌊a⌋ + ⌊-a⌋ : ℚ) ≤ (-2 : ℚ) := by 
        exact_mod_cast h11
      linarith
    omega
  have h7 : ⌊a⌋ + ⌊-a⌋ = 0 ∨ ⌊a⌋ + ⌊-a⌋ = -1 := by 
    have h8 : ⌊a⌋ + ⌊-a⌋ ≤ 0 := by 
      omega
    have h9 : ⌊a⌋ + ⌊-a⌋ > -2 := by 
      omega
    have h10 : ⌊a⌋ + ⌊-a⌋ ≥ -1 := by 
      omega
    omega
  exact h7