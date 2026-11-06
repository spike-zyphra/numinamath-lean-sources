import Mathlib

theorem algebra_209652 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : ∃ x, a * (b + c + d) = x ∧ b * (a + c + d) = x ∧ c * (a + b + d) = x ∧ d * (a + b + c) = x) :
    a ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2 ∧ c ^ 2 = d ^ 2 := by

  rcases h with ⟨x, h1, h2, h3, h4⟩

  have eq1 : a * (b + c + d) = b * (a + c + d) := by linarith
  have eq3 : c * (a + b + d) = d * (a + b + c) := by linarith [h3, h4]

  have eq2 : a * (c + d) = b * (c + d) := by
    nlinarith [eq1]

  have eq4 : c * (a + b) = d * (a + b) := by
    nlinarith [eq3]

  by_cases h5 : a + b = 0

  · -- Case where $a + b = 0$
    have h6 : a = -b := by linarith
    have h7 : a^2 = b^2 := by
      rw [show a = -b by linarith [h6]]
      ring
    -- Now need to show c^2 = d^2
    have eq6 : c * (a + b) = d * (a + b) := by 
      linarith [eq4, h5]
    have eq7 : c * 0 = d * 0 := by
      rw [show (a + b) = 0 by linarith [h5]] at eq6
      linarith
    -- Simplifying this gives 0 = 0, which doesn't add new information
    -- Need to derive from original equations

    -- From h1: a * (b + c + d) = x
    -- From h2: b * (a + c + d) = x
    -- With a = -b, these give us equations involving c and d
    have eq8 : x = a * (b + c + d) := by
      linarith
    have eq9 : x = b * (a + c + d) := by
      linarith
    -- Substituting a = -b to get explicit equations
    rw [show a = -b by linarith [h6]] at eq8
    rw [show a = -b by linarith [h6]] at eq9

    -- From substituting a = -b:
    -- eq8: x = -b * (b + c + d)
    -- eq9: x = b * (-b + c + d)
    -- Now equate eq8 and eq9:
    have eq10 : -b * (b + c + d) = b * (-b + c + d) := by 
      linarith
    -- Simplify to derive relationship between c and d
    have eq11 : -b^2 - b*c - b*d = -b^2 + b*c + b*d := by
      nlinarith [eq10]

    -- Simplifies to: -2b*c - 2b*d = 0
    -- Since b ≠ 0, we get: -(c + d) = 0 or c + d = 0
    have eq12 : c + d = 0 := by
      apply (mul_left_inj' hb).mp 
      nlinarith [eq11]
    -- Now using eq12: c + d = 0, we can prove c^2 = d^2
    have h8 : c^2 = d^2 := by 
      have h9 : d = -c := by linarith [eq12]
      rw [show d = -c by linarith [eq12]]
      nlinarith
    have hb2 : b^2 = c^2 := by 
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
    exact ⟨h7, hb2, h8⟩

  · -- Case where $a + b ≠ 0$
    have hcd : c = d := by
      apply (mul_left_inj' (show (a + b) ≠ 0 by
        assumption)).mp 
      linarith [eq4]
    
    -- Now using the equality from eq1
    have eq5 : a * (c + d) = b * (c + d) := by
      nlinarith [eq1]

    -- Since c + d ≠ 0 (if it was, then would be problem, but since hc and hd are non-zero)
    have hab : a = b := by 
      have h6 : c + d = 2 * c := by
        rw [show d = c by linarith [hcd]]
        ring 
      rw [h6] at eq5 
      have h7 : a * (2 * c) = b * (2 * c) := by 
        linarith [eq5]
      have h8 : a = b := by
        apply (mul_left_inj' (show (2 * c) ≠ 0 by
          intro h'
          have : c = 0 := by linarith 
          contradiction)).mp 
        linarith [h7]
      linarith [h8]

    -- Now using the equalities hcd and hab
    -- Let's derive b^2 = c^2
    have hb2 : b^2 = c^2 := by 
      have h5 : d = c := by linarith [hcd]
      have eq6 : d * (a + b + c) = a * (b + c + d) := by 
        nlinarith [h1, h2, h3, h4, hab, hcd]
      rw [show d = c by linarith [hcd], show a = b by linarith [hab]] at eq6
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]

    have ha2 : a^2 = b^2 := by 
      rw [show a = b by linarith [hab]]

    have h15 : c^2 = d^2 := by 
      rw [show c = d by linarith [hcd]]
    
    exact ⟨ha2, hb2, h15⟩