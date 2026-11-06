import Mathlib

theorem algebra_212733 (x : Fin 8 → ℝ)
    (h1 : x 0 + x 1 + x 2 = 6)
    (h2 : x 1 + x 2 + x 3 = 9)
    (h3 : x 2 + x 3 + x 4 = 3)
    (h4 : x 3 + x 4 + x 5 = -3)
    (h5 : x 4 + x 5 + x 6 = -9)
    (h6 : x 5 + x 6 + x 7 = -6)
    (h7 : x 6 + x 7 + x 0 = -2)
    (h8 : x 7 + x 0 + x 1 = 2) :
    x = ![1, 2, 3, 4, -4, -3, -2, -1] := by
  funext i
  fin_cases i <;> simp [Fin.isValue] at *
  <;> try { aesop }
  <;> try { 
    norm_num 
    all_goals try { tauto } 
  }
  <;> try { 
    have h9 : x 0 = 1 := by
      linarith 
    have h91 : x 1 = 2 := by 
      linarith 
    have h92 : x 2 = 3 := by 
      linarith
    have h93 : x 3 = 4 := by
      linarith
    have h94 : x 4 = -4 := by
      linarith
    have h95 : x 5 = -3 := by
      linarith
    have h96 : x 6 = -2 := by
      linarith
    have h97 : x 7 = -1 := by
      linarith
    simp [h9, h91, h92, h93, h94, h95, h96, h97] at *
    all_goals try { linarith }
    all_goals try { tauto } 
  }
  <;> try { 
    norm_num 
    all_goals try { tauto } 
    all_goals try { 
      linarith 
    }
  }
  <;> try { 
    all_goals try { 
      nlinarith 
      all_goals try { tauto } 
    }
  }