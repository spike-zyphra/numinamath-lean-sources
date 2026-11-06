import Mathlib

theorem algebra_93989 (a b c d e f : ℤ) (h₀ : a + b = 26) (h₁ : a + b + c + d = 41)
    (h₂ : a + b + c + d + e + f = 57) :
    Odd a ∨ Odd b ∨ Odd c ∨ Odd d ∨ Odd e ∨ Odd f := by 
  by_contra h
  push_neg at h 
  have ha : Even a := by 
    simpa using h.1
  have hb : Even b := by 
    simpa using h.2.1
  have hc : Even c := by 
    simpa using h.2.2.1
  have hd : Even d := by 
    simpa using h.2.2.2.1
  have he : Even e := by 
    simpa using h.2.2.2.2.1
  have hf : Even f := by 
    simpa using h.2.2.2.2.2
  rcases ha with ⟨ka, hha⟩
  rcases hb with ⟨kb, hhb⟩
  rcases hc with ⟨kc, hhc⟩
  rcases hd with ⟨kd, hhd⟩
  rcases he with ⟨ke, hhe⟩
  rcases hf with ⟨kf, hhf⟩
  -- Now, substitute these into the given equations 
  -- From h₀: a + b = 26
  have h3 : ka + kb = 13 := by 
    linarith 
  -- From h₁: a + b + c + d = 41 
  have h4 : ka + kb + kc + kd = 20 := by 
    omega 
  -- This leads to a contradiction, as 20.5 must be integer 
  omega