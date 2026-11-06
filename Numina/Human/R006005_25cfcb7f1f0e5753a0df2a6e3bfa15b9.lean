import Mathlib

/- 
A conical flask contains some water. When the flask is oriented so that its base is horizontal and lies at the bottom (so that the vertex is at the top), the water is 1 inch deep. When the flask is turned upside-down, so that the vertex is at the bottom, the water is 2 inches deep. What is the height of the cone?
-/

theorem geometry_611038 : 
    -- The height of the cone is 1/2 + √93/6
    ∃ h : ℝ, (3*h^2 - 3*h - 7 = 0) ∧ (h > 0) ∧ h = (1 : ℝ)/2 + Real.sqrt 93/6 :=
  -- Using a direct proof instead of by-tactics to avoid issues with trailing text
  let h := (1 : ℝ)/2 + Real.sqrt 93/6;
  
  -- First fact: h satisfies the quadratic equation
  have h_eq : 3*h^2 - 3*h - 7 = 0 := by 
    dsimp[h]
    ring_nf
    field_simp
    norm_num
  
  -- Second fact: h is positive
  have h_pos : h > 0 := 
    have h1 : (1 : ℝ)/2 > 0 := by norm_num;
    have h3 : Real.sqrt 93/6 > 0 := by positivity;
    add_pos h1 h3;
  
  -- Combine the results
  Exists.intro h (And.intro h_eq (And.intro h_pos rfl))