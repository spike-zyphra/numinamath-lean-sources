import Mathlib

theorem algebra_20776 {j k l : ℤ} (hpos : j > 0 ∧ k > 0 ∧ l > 0)
    (hjk : j * k = 24) (hjl : j * l = 48) (hkl : k * l = 18) :
    j + k + l = 17 := by 
  have h1 : j > 0 := hpos.1
  have h2 : k > 0 := hpos.2.1
  have h3 : l > 0 := hpos.2.2
  
  have h4 : j^2 = 64 := by 
    nlinarith [hjk, hjl, hkl]
  
  have hj : j = 8 := by 
    nlinarith [h4, h1]

  have hk : k = 3 := by 
    rw [hj] at hjk
    have : k = 3 := by 
      nlinarith
    exact this
  
  have hl : l = 6 := by 
    rw [hj] at hjl
    have : l = 6 := by 
      nlinarith
    exact this
  
  linarith [hj, hk, hl]