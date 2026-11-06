import Mathlib

theorem algebra_194556 {x : ℂ} (hx : x^2 + x + 1 = 0) :
    x^14 + 1 / x^14 = -1 := by
  have h1 : x ≠ 0 := by 
    by_contra h
    rw [h] at hx
    norm_num at hx

  have h2 : x^3 = 1 := by 
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-x -1) := by 
        have h_eq : x^2 = -x -1 := by 
          calc 
            x^2 = x^2 + x +1 -x -1 := by ring
            _ = (-x -1) := by 
              rw [hx]
              all_goals ring
        rw [h_eq]
      _ = -x^2 -x := by ring
      _ = -(-x -1) -x := by 
        rw [show x^2 = -x -1 by 
          calc 
            x^2 = x^2 + x +1 -x -1 := by ring
            _ = (-x -1) := by 
              rw [hx]
              all_goals ring
        ]
      _ = 1 := by ring
  
  have h3 : x^14 = x^2 := by
    calc 
      x^14 = (x^3)^4 * x^2 := by ring
      _ = (1)^4 * x^2 := by 
        rw [h2]
      _ = x^2 := by ring
  
  -- Derive 1/x = -x -1 to compute 1/x^2
  have h5 : 1 / x = -x - 1 := by 
    have h6 : x ≠ 0 := h1
    have eq1 : x^2 + x + 1 = 0 := hx
    have eq2 : 1 / x = (-x - 1) := by 
      -- Multiply by 1/x to get expression
      have eq3 : x^2 + x + 1 = 0 := hx
      have eq4 : x + 1 + (1 / x) = 0 := by 
        have eq5 : x^2 + x +1 = 0 := hx
        have eq6 : x ≠ 0 := h1
        calc
          x + 1 + (1 / x) = (x^2 + x + 1) / x := by 
            field_simp [h1]
            <;> ring
          _ = (0) / x := by 
            rw [hx]
          _ = 0 := by 
            simp
      have eq7 : (1 / x) = -x - 1 := by 
        calc
          (1 / x) = (x + 1 + (1 / x)) - x -1 := by ring
          _ = (0) - x -1 := by 
            rw [eq4]
          _ = -x -1 := by ring
      exact_mod_cast eq7
    exact_mod_cast eq2
  
  have h8 : 1 / x^2 = x := by
    calc 
      1 / x^2 = (1 / x) ^ 2 := by 
        field_simp [h1]
      _ = (-x -1) ^2 := by 
        rw [h5]
      _ = x^2 + 2 *x +1 := by 
        ring
      _ = (-x -1) + 2*x +1 := by 
        rw [show x^2 = -x -1 by 
          calc 
            x^2 = x^2 + x +1 -x -1 := by ring
            _ = (-x -1) := by 
              rw [hx]
              <;> ring
        ]
      _ = x := by ring
  
  have h9 : x^14 + 1 / x^14 = x^2 +1 / x^2 := by 
    rw [h3]

  have h10 : x^2 +1 / x^2 = -1 := by
    have h11 :1 /x^2 = x := h8
    rw [h11]
    have h12 : x^2 + x = -1 := by
      have h12 : x^2 +x +1 = 0 := by 
        exact_mod_cast hx
      calc 
        x^2 +x = (x^2 +x +1) -1 := by ring
        _ = (0) -1 := by 
          rw [h12]
        _ = -1 := by ring
    calc
      x^2 + x = x^2 +x := by ring
      _ = -1 := h12
  
  rw [h9]
  exact_mod_cast h10