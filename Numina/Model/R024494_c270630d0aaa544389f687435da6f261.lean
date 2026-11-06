import Mathlib

theorem algebra_102140 (a : Fin 5 → ℝ) (ha : ∀ i j, i < j → a i > a j)
    (x : Fin 5 → ℝ) (h : ∀ i, x i + x ((i + 1) % 5) + x ((i + 2) % 5) = a i) :
    x 2 > x 0 ∧ x 0 > x 3 ∧ x 3 > x 1 ∧ x 1 > x 4 := by

  have h1 : x 0 + x 1 + x 2 = a 0 := by 
    specialize h 0 
    simpa using h
  have h2 : x 1 + x 2 + x 3 = a 1 := by
    specialize h 1 
    simpa using h
  have h3 : x 2 + x 3 + x 4 = a 2 := by 
    specialize h 2 
    simpa using h 
  have h4 : x 3 + x 4 + x 0 = a 3 := by
    specialize h 3 
    simpa using h 
  have h5 : x 4 + x 0 + x 1 = a 4 := by 
    specialize h 4 
    simpa using h

  have h21 : x 2 > x 0 := by
    have eq3 : x 2 - x 0 = a 2 - a 3 := by
      linarith 
    have ha23 : a 2 > a 3 := by
      apply ha 2 3 
      simp 
    linarith [eq3, ha23]

  have h22 : x 0 > x 3 := by 
    have eq1 : x 0 - x 3 = a 0 - a 1 := by 
      linarith 
    have ha10 : a 0 > a 1 := by 
      apply ha 0 1 
      simp 
    linarith [eq1, ha10]

  have h23 : x 3 > x 1 := by 
    have eq4 : x 3 - x 1 = a 3 - a 4 := by 
      linarith 
    have ha34 : a 3 > a 4 := by 
      apply ha 3 4 
      simp 
    linarith [eq4, ha34]

  have h24 : x 1 > x 4 := by
    have eq2 : x 1 - x 4 = a 1 - a 2 := by 
      linarith 
    have ha12 : a 1 > a 2 := by 
      apply ha 1 2 
      simp 
    linarith [eq2, ha12]

  exact ⟨h21, h22, h23, h24⟩