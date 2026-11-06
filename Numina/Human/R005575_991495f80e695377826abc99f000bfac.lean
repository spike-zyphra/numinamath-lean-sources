import Mathlib

open Real

/- 
Problem:
In-Young generates a string of B zeroes and ones using the following method: What is the expected value of the number of zeroes in her string?
-/
theorem combinatorics_608929 
    {A B C : ℝ} 
    (hA : A > 0) 
    (hB : B > 0)
    (hC : C > 0) 
    (h1 : C = B / 2)
    (h2 : A * (2 * B + C) = 2) 
    (h3 : 2 * A * (B + 1) * (C + 1) = B + C) :
    A = 1 / 5 ∧ B = 4 ∧ C = 2 := by

  have h4 : C ≠ 0 := by linarith

  rw [h1] at h2 h3

  have h5 : B = 4 := by nlinarith

  have h6 : A = 1 / 5 := by nlinarith

  have h7 : C = 2 := by nlinarith

  exact ⟨h6 , h5 , h7⟩
   
  
  