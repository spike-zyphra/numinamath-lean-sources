import Mathlib

theorem algebra_132419 (x y z : ℝ)
    (h1 : x^2 + y^2 + 8 * x - 6 * y = -20)
    (h2 : x^2 + z^2 + 8 * x + 4 * z = -10)
    (h3 : y^2 + z^2 - 6 * y + 4 * z = 0) :
    (x, y, z) = (-3, 1, 1) ∨ (x, y, z) = (-3, 1, -5) ∨
    (x, y, z) = (-3, 5, 1) ∨ (x, y, z) = (-3, 5, -5) ∨
    (x, y, z) = (-5, 1, 1) ∨ (x, y, z) = (-5, 1, -5) ∨
    (x, y, z) = (-5, 5, 1) ∨ (x, y, z) = (-5, 5, -5) := by
  have eq1 : (x + 4) ^ 2 + (y - 3) ^ 2 = 5 := by 
    nlinarith 
  -- Equation 2 in completed square form.
  have eq2 : (x + 4) ^ 2 + (z + 2) ^ 2 = 10 := by
    nlinarith 
  -- Equation 3 in completed square form.
  have eq3 : (y - 3) ^ 2 + (z + 2) ^ 2 = 13 := by
    nlinarith 
  -- Sum of all three equations.
  have eq4 : (x + 4) ^ 2 + (y - 3) ^ 2 + (z + 2) ^ 2 = 14 := by
    nlinarith [eq1, eq2, eq3]
  -- Solving for z using eq4 and eq1.
  have eq5 : (z + 2) ^ 2 = 9 := by
    nlinarith [eq1, eq4]
  -- Solving for z.
  have h4 : z + 2 = 3 ∨ z + 2 = -3 := by 
    have : (z + 2) ^ 2 - 9 = 0 := by linarith [eq5]
    have : (z + 2 - 3) * (z + 2 + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 this) with h5 h6
    · left 
      linarith 
    · right 
      linarith
  cases h4 with
  | inl h7 => 
    have h8 : z = 1 := by linarith
    -- Solving for y using eq3 and z.
    have eq6 : (y - 3) ^ 2 = 4 := by 
      nlinarith [eq3, h7]
    -- Solving for y.
    have eq7 : y - 3 = 2 ∨ y - 3 = -2 := by 
      have : (y - 3) ^ 2 - 4 = 0 := by linarith [eq6]
      have : (y - 3 - 2) * (y - 3 + 2) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.1 this) with h5 h6 
      · left 
        linarith 
      · right 
        linarith 
    -- Solving for x using eq1 and y.
    have eq8 : (x + 4) ^ 2 = 1 := by
      nlinarith [eq1, eq6, h7]
    -- Solving for x.
    have eq9 : x + 4 = 1 ∨ x + 4 = -1 := by
      have : (x + 4) ^ 2 - 1 = 0 := by linarith [eq8]
      have : (x + 4 - 1) * (x + 4 + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 this) with h5 h6 
      · left 
        linarith 
      · right 
        linarith 
    cases eq7 with
    | inl h10 => 
      cases eq9 with 
      | inl h11 => 
        have hx1 : x = -3 := by linarith 
        have hy1 : y = 5 := by linarith 
        have hz1 : z = 1 := by linarith 
        simp [hx1, hy1, hz1]
      | inr h12 => 
        have hx2 : x = -5 := by linarith 
        have hy2 : y = 5 := by linarith 
        have hz2 : z = 1 := by linarith 
        simp [hx2, hy2, hz2]
    | inr h10 => 
      cases eq9 with 
      | inl h11 => 
        have hx1 : x = -3 := by linarith 
        have hy1 : y = 1 := by linarith 
        have hz1 : z = 1 := by linarith 
        simp [hx1, hy1, hz1]
      | inr h12 => 
        have hx2 : x = -5 := by linarith 
        have hy2 : y = 1 := by linarith 
        have hz2 : z = 1 := by linarith 
        simp [hx2, hy2, hz2]
  | inr h7 => 
    have h8 : z = -5 := by linarith
    -- Solving for y using eq3 and z.
    have eq6 : (y - 3) ^ 2 = 4 := by 
      nlinarith [eq3, h7]
    -- Solving for y.
    have eq7 : y - 3 = 2 ∨ y - 3 = -2 := by
      have : (y - 3) ^ 2 - 4 = 0 := by linarith [eq6]
      have : (y - 3 - 2) * (y - 3 + 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 this) with h5 h6 
      · left 
        linarith 
      · right 
        linarith 
    -- Solving for x using eq1 and y.
    have eq8 : (x + 4) ^ 2 = 1 := by 
      nlinarith [eq1, eq6, h7]
    -- Solving for x.
    have eq9 : x + 4 = 1 ∨ x + 4 = -1 := by
      have : (x + 4) ^ 2 - 1 = 0 := by linarith [eq8]
      have : (x + 4 - 1) * (x + 4 + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 this) with h5 h6 
      · left 
        linarith 
      · right 
        linarith 
    cases eq7 with 
    | inl h10 => 
      cases eq9 with 
      | inl h11 => 
        have hx1 : x = -3 := by linarith 
        have hy1 : y = 5 := by linarith 
        have hz1 : z = -5 := by linarith 
        simp [hx1, hy1, hz1]
      | inr h12 => 
        have hx2 : x = -5 := by linarith 
        have hy2 : y = 5 := by linarith 
        have hz2 : z = -5 := by linarith 
        simp [hx2, hy2, hz2]
    | inr h10 => 
      cases eq9 with 
      | inl h11 => 
        have hx1 : x = -3 := by linarith 
        have hy1 : y = 1 := by linarith 
        have hz1 : z = -5 := by linarith 
        simp [hx1, hy1, hz1]
      | inr h12 => 
        have hx2 : x = -5 := by linarith 
        have hy2 : y = 1 := by linarith 
        have hz2 : z = -5 := by linarith 
        simp [hx2, hy2, hz2]