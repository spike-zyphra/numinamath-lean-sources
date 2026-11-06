import Mathlib

theorem number_theory_275566 {A B : ℤ} (hA : A > B) :
    3 ∣ A ∨ 3 ∣ B ∨ 3 ∣ A + B ∨ 3 ∣ A - B := by
  have h1 : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by
    omega
  have h2 : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by
    omega
  rcases h1 with hA0 | hA1 | hA2
  · -- Case A % 3 = 0
    have h3 : 3 ∣ A := by
      omega
    left
    exact h3
  · -- Case A % 3 = 1
    rcases h2 with hB0 | hB1 | hB2
    · -- Case B % 3 = 0
      have h4 : 3 ∣ B := by
        omega
      right
      left
      exact h4
    · -- Case B % 3 = 1
      have h5 : (A - B) % 3 = 0 := by 
        omega
      have h6 : 3 ∣ A - B := by
        omega
      right
      right
      right
      exact h6
    · -- Case B % 3 = 2
      have h7 : (A + B) % 3 = 0 := by 
        omega
      have h8 : 3 ∣ A + B := by
        omega
      right
      right
      left
      exact h8
  · -- Case A % 3 = 2
    rcases h2 with hB0 | hB1 | hB2
    · -- Case B % 3 = 0 
      have h9 : 3 ∣ B := by 
        omega
      right
      left
      exact h9
    · -- Case B % 3 = 1 
      have h10 : (A + B) % 3 = 0 := by 
        omega
      have h11 : 3 ∣ A + B := by 
        omega
      right
      right
      left
      exact h11
    · -- Case B % 3 = 2 
      have h12 : (A - B) % 3 = 0 := by 
        omega
      have h13 : 3 ∣ A - B := by 
        omega
      right
      right
      right
      exact h13