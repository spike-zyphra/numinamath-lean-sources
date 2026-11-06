import Mathlib

theorem algebra_112747 (a b c : ℝ) (ha : a^3-3*a+1=0) (hb : b^3-3*b+1=0) (hc : c^3-3*c+1=0)
    (hroots : a≠b ∧ a≠c ∧ b≠c) : a^4+b^4+c^4=18 := by
  have ha1 : a^3 = 3 * a - 1 := by linarith
  have hb1 : b^3 = 3 * b - 1 := by linarith
  have hc1 : c^3 = 3 * c - 1 := by linarith

  -- Derive expressions for a^4, b^4, c^4
  have ha4 : a^4 = 3 * a^2 - a := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (3 * a - 1) := by rw [ha1]
      _ = 3 * a^2 - a := by ring

  have hb4 : b^4 = 3 * b^2 - b := by
    calc
      b^4 = b * b^3 := by ring
      _ = b * (3 * b - 1) := by rw [hb1]
      _ = 3 * b^2 - b := by ring

  have hc4 : c^4 = 3 * c^2 - c := by
    calc
      c^4 = c * c^3 := by ring
      _ = c * (3 * c - 1) := by rw [hc1]
      _ = 3 * c^2 - c := by ring

  -- Show that a^4 + b^4 + c^4 = 3 * (a^2 + b^2 + c^2) - (a + b + c)
  have h : a^4 + b^4 + c^4 = 3 * (a^2 + b^2 + c^2) - (a + b + c) := by 
    linarith [ha4, hb4, hc4]

  -- Derive a + b + c = 0
  have h_eq1 : a^2 + a * b + b^2 = 3 := by
    have eq1 : a^3 - b^3 = 3 * (a - b) := by linarith [ha1, hb1]
    have hne1 : a - b ≠ 0 := by
      intro h
      apply hroots.1
      linarith
    have eq2 : (a - b) * (a^2 + a * b + b^2) = 3 * (a - b) := by
      nlinarith 
    have : a^2 + a * b + b^2 = 3 := by
      apply (mul_left_inj' hne1).mp
      linarith 
    linarith

  have h_eq2 : a^2 + a * c + c^2 = 3 := by
    have eq1 : a^3 - c^3 = 3 * (a - c) := by linarith [ha1, hc1]
    have hne1 : a - c ≠ 0 := by
      intro h
      apply hroots.2.1
      linarith
    have eq2 : (a - c) * (a^2 + a * c + c^2) = 3 * (a - c) := by
      nlinarith 
    have : a^2 + a * c + c^2 = 3 := by
      apply (mul_left_inj' hne1).mp
      linarith 
    linarith

  have h_eq3 : b^2 + b * c + c^2 = 3 := by
    have eq1 : b^3 - c^3 = 3 * (b - c) := by linarith [hb1, hc1]
    have hne1 : b - c ≠ 0 := by
      intro h
      apply hroots.2.2
      linarith
    have eq2 : (b - c) * (b^2 + b * c + c^2) = 3 * (b - c) := by
      nlinarith 
    have : b^2 + b * c + c^2 = 3 := by
      apply (mul_left_inj' hne1).mp
      linarith 
    linarith

  -- From these equations derive a + b + c = 0
  have h_eq4 : a + b + c = 0 := by
    have eq1 : (b - c) * (a + b + c) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp eq1) with h1 h2
    · -- case b - c = 0
      exfalso
      apply hroots.2.2
      linarith 
    · -- case a + b + c = 0
      linarith 

  -- From a + b + c = 0 derive a^2 + b^2 + c^2 = 6
  have h_eq5 : a^2 + b^2 + c^2 = 6 := by
    have h_eq6 : a + b + c = 0 := h_eq4
    have h_eq7 : a * b + b * c + c * a = -3 := by
      nlinarith 
    nlinarith 
  -- Now prove the goal using the computed values
  rw [h, h_eq4, h_eq5]
  all_goals linarith
  all_goals norm_num
  all_goals linarith