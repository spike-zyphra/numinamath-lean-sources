import Mathlib

theorem algebra_3684 {a b c : ℝ} (h0 : 2017*(a-b)+2018*(b-c)+2019*(c-a)=0) (h1 : 2017^2*(a-b)+2018^2*(b-c)+2019^2*(c-a)=2018) : c-a=1009 := by
  have eq3 : b + c = 2 * a := by
    linarith
  
  have h2 : c - a = a - b := by
    linarith [eq3]

  have h3 : b - c = -2 * (c - a) := by 
    linarith [eq3]

  rw [h3] at h1 
  rw [show a - b = c - a by linarith [h2]] at h1

  have h5 : (c - a) * (2017^2 - 2 * 2018^2 + 2019^2 : ℝ) = 2018 := by
    linarith
  
  have h6 : (2017^2 - 2 * 2018^2 + 2019^2 : ℝ) = 2 := by
    norm_num
  
  rw [h6] at h5
  have h7 : c - a = 1009 := by 
    linarith
  
  linarith [h7]