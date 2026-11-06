import Mathlib

/- Tom, Dorothy, and Sammy went on a vacation and agreed to split the costs evenly.  
During their trip Tom paid $105, Dorothy paid $125, and Sammy paid $175.  
In order to share costs equally, Tom gave Sammy t dollars, and Dorothy gave Sammy d dollars.  
What is t−d?
(A) 15(B) 20(C) 25(D) 30(E) 35 -/

theorem algebra_94245 (t d : ℝ)
(h : 105 + t = (105 + 125 + 175) / 3 ∧ d + 125 = (105 + 125 + 175) / 3) :
t - d = 20 := by
--Both 105 + t and 125 + d equal the mean. By setting the equality 105 + t = d + 125 the claim follows.
  obtain ⟨h₁, h₂⟩:= h
  rw[← h₂] at h₁
  linarith