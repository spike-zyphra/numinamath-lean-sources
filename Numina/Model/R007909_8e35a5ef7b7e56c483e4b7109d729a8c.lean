import Mathlib

theorem algebra_22179 {f : ℝ → ℝ} (hf : ∃ a b c d, a ≠ 0 ∧ f = fun x => a*x^3 + b*x^2 + c*x + d)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2) (h3 : f 3 = 4) :
    f 5 = 15 := by
  rcases hf with ⟨a, b, c, d, ha, hf⟩

  have h_eq0 : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = 0 := by
    rw [hf] at h0
    simpa using h0
  
  have h_eq1 : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 1 := by 
    rw [hf] at h1
    simpa using h1
  
  have h_eq2 : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 2 := by 
    rw [hf] at h2
    simpa using h2
  
  have h_eq3 : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 4 := by 
    rw [hf] at h3
    simpa using h3
  
  have hd : d = 0 := by linarith
  
  have h_eq1' : a + b + c = 1 := by 
    rw [hd] at h_eq1
    linarith
  
  have h_eq2' : 8 * a + 4 * b + 2 * c = 2 := by 
    rw [hd] at h_eq2
    linarith
  
  have h_eq3' : 27 * a + 9 * b + 3 * c = 4 := by 
    rw [hd] at h_eq3
    linarith

  have h_eq4 : 3 * a + b = 0 := by 
    linarith [h_eq1', h_eq2']
  
  have h_eq5 : 5 * a + b = 1 / 3 := by 
    linarith [h_eq2', h_eq3']

  have h_eq6 : a = 1 / 6 := by 
    linarith [h_eq4, h_eq5]

  have h_eq7 : b = -1 / 2 := by 
    linarith [h_eq4, h_eq6]

  have h_eq8 : c = 4 / 3 := by 
    linarith [h_eq1', h_eq6, h_eq7]

  have h5 : f 5 = a * 5 ^ 3 + b * 5 ^ 2 + c * 5 + d := by 
    rw [hf]

  rw [h5]
  rw [h_eq6, h_eq7, h_eq8, hd]
  norm_num