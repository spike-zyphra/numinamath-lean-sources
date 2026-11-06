import Mathlib

theorem algebra_100193 (a b c d e f : ℝ)
    (h₀ : a = (b + c + d) / 3) (h₁ : b = (a + c + e) / 3)
    (h₂ : c = (a + b + f) / 3) (h₃ : d = (a + e + f) / 3)
    (h₄ : e = (b + d + f) / 3) (h₅ : f = (c + d + e) / 3) :
    a = b ∧ b = c ∧ c = d ∧ d = e ∧ e = f := by 
  have eq0a : 3 * a = b + c + d := by
    linarith [h₀]
  have eq1a : 3 * b = a + c + e := by
    linarith [h₁]
  have eq2a : 3 * c = a + b + f := by
    linarith [h₂]
  have eq3a : 3 * d = a + e + f := by
    linarith [h₃]
  have eq4a : 3 * e = b + d + f := by
    linarith [h₄]
  have eq5a : 3 * f = c + d + e := by
    linarith [h₅]

  constructor
  · -- Show a = b
    have ha : a = c := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a]
    have hb : b = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha]
    linarith [hb]
  
  constructor
  · -- Show b = c 
    have ha : a = c := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a]
    have hb : b = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha]
    linarith [hb, ha]
  
  constructor
  · -- Show c = d 
    have ha : a = c := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a]
    have hd : d = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha]
    linarith [ha, hd]
  
  constructor
  · -- Show d = e 
    have ha : a = c := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a]
    have hd : d = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha]
    have he : e = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha, hd]
    linarith [hd, he]
  
  · -- Show e = f 
    have ha : a = c := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a]
    have he : e = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha]
    have hf : f = a := by 
      linarith [eq0a, eq1a, eq2a, eq3a, eq4a, eq5a, ha, he]
    linarith [he, hf]