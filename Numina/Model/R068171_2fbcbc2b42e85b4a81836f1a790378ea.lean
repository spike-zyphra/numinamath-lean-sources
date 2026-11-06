import Mathlib

theorem algebra_179157 {x y z : ℝ} (h1 : 2*x-3*y-z=0) (h2 : x+3*y-14*z=0) (hz : z≠0) :
    (x^2+3*x*y)/(y^2+z^2)=7 := by 
  have eq1 : x = 5*z := by
    have h3 : 3*x = 15*z := by 
      linarith [h1, h2]
    linarith
  
  have eq2 : y = 3*z := by 
    rw [eq1] at h1
    linarith

  have h3 : x^2 + 3*x*y = 70*z^2 := by 
    rw [eq1, eq2]
    linarith [pow_two_nonneg z]

  have h4 : y^2 + z^2 = 10*z^2 := by 
    rw [eq2]
    linarith [pow_two_nonneg z]

  have h5 : (x^2 + 3*x*y) / (y^2 + z^2) = (70*z^2) / (10*z^2) := by 
    rw [h3, h4]

  have h6 : (70*z^2) / (10*z^2) = 7 := by 
    have h7 : z^2 ≠ 0 := by 
      intro h
      apply hz
      nlinarith
    field_simp [h7]
    <;> ring_nf <;> linarith
  
  rw [h5, h6]
  all_goals linarith [hz]