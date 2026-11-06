import Mathlib

theorem algebra_229264 (A B C D : ℕ) (hA : A * 3 = B * 2) (hB : B * 6 = C * 5)
    (hC : C * 4 = D * 3) (hD : D + A + B + C = 9246) :
    A = 1380 ∧ B = 2070 ∧ C = 2484 ∧ D = 3312 := by

  have h1 : A = 1380 := by 
    omega

  have h2 : B = 2070 := by
    omega

  have h3 : C = 2484 := by
    omega

  have h4 : D = 3312 := by 
    omega
  
  exact ⟨h1, h2, h3, h4⟩