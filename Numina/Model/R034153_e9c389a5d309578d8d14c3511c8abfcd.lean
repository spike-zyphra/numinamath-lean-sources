import Mathlib

theorem algebra_204846 {x : ℂ} (hx : x^2 + x + 1 = 0) :
    x^14 + 1 / x^14 = -1 := by 
  have hx1 : x ≠ 0 := by 
    by_contra h
    rw [h] at hx
    norm_num [h] at hx 
  have h1 :x ^ 3 =1 := by 
    have eq1 :x^2 +x +1 =0 := hx 
    calc 
      x ^3 = x * x^2 := by ring 
      _ = x * (-x -1) := by
        have eq1' :x^2 = -x -1 := by 
          have eq2 : x^2 +x +1 =0 := hx 
          calc 
            x^2 = (x ^ 2 +x +1) -x -1 := by ring 
            _ = 0 -x -1 := by rw [eq2]
            _ = -x -1 := by ring 
        rw [eq1']
      _ = -x ^2 -x := by ring 
      _ = -(-x -1) -x := by
        have eq1' :x ^2 = -x -1 := by 
          have eq2 : x^2 +x +1 =0 := hx 
          calc 
            x^2 = (x^2 +x +1) -x -1 := by ring 
            _ = 0 -x -1 := by rw [eq2]
            _ = -x -1 := by ring 
        rw [eq1']
      _ =(x +1) -x := by ring 
      _ =1 := by ring
  have eq4 :x ^ 14 =x^2 := by 
    calc 
      x ^14 = (x^3) ^4 * x^2 := by ring
      _ =1^4 * x^2 := by rw [h1]
      _ =1 * x^2 := by simp 
      _ =x^2 := by ring 
  have eq3 :x^2 ≠0 := by 
    by_contra h 
    have :x =0 := by
      have h_eq :x ^2 = 0 := by simpa using h 
      have :x *x = 0 := by 
        calc 
          x *x =x ^2 := by ring 
          _ =0 := h_eq 
      cases' (mul_eq_zero.mp this) with h4 h4 
      · -- x = 0 
        exact_mod_cast h4 
      · -- x = 0 
        exact_mod_cast h4 
    contradiction 
  have eq5 :x * x^2 =1 := by 
    calc
      x *x^2 =x ^3 := by ring 
      _ =1 :=by rw [h1] 
  have eq6 : 1 /x^2 =x := by
    have eq3' : x ≠ 0 := hx1 
    have eq6 : 1 /x^2 =x := by
      have hne1 : x ≠ 0 := hx1 
      have hne2 : x^2 ≠ 0 := eq3 
      field_simp [hne1, hne2] at *
      <;> ring_nf at eq5 ⊢
      all_goals
        try tauto 
    exact_mod_cast eq6 
  have h3 :1 /x^14 =x := by
    rw [eq4]
    rw [eq6] 
  rw [h3]
  rw [eq4]
  have eq3' :x^2 +x = -1 := by 
    have eq4' :x^2 +x +1 = 0 := hx 
    calc 
      x^2 +x = (x^2 +x +1) -1 := by ring 
      _ = 0 -1 := by rw [eq4']
      _ =-1 := by ring 
  tauto