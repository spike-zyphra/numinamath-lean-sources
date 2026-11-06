import Mathlib

theorem algebra_118553 (f : ℝ → ℝ) (hf : f = fun x => x^3 - 84 * x)
    (a b c : ℝ) (ha : f a = M) (hb : f b = M) (hc : f c = M)
    (hord : a < b ∧ b < c) (hdist : |a - b| = (1 / 2) * |b - c|) :
    M = 160 := by

  have h1 : a ^ 3 - 84 * a = M := by 
    rw [hf] at ha
    simp at ha
    linarith

  have h2 : b ^ 3 - 84 * b = M := by 
    rw [hf] at hb
    simp at hb
    linarith

  have h3 : c ^ 3 - 84 * c = M := by 
    rw [hf] at hc
    simp at hc
    linarith

  have h4 : a < b := hord.1
  have h5 : b < c := hord.2

  have eq1 : |a - b| = b - a := by 
    rw [abs_of_neg (show a - b < 0 by linarith)]
    all_goals linarith

  have eq2 : |b - c| = c - b := by 
    rw [abs_of_neg (show b - c < 0 by linarith)]
    all_goals linarith

  rw [eq1, eq2] at hdist

  -- From hdist equation: b - a = (1/2) * (c - b), multiplied by 2: 2 * (b - a) = c - b, expanded to 2b - 2a = c - b, rearranged to 3b = 2a + c
  have h7 : 3 * b = 2 * a + c := by
    nlinarith

  -- Subtract the first and the second root equation: (A^3 - 84A) - (b^3 - 84 b) = 0
  have eq3 : a ^ 2 + a * b + b ^ 2 = 84 := by 
    have eq4 : a ^ 3 - 84 * a = M := h1 
    have eq5 : b ^ 3 - 84 * b = M := h2 
    have eq6 : a ^ 3 - 84 * a - (b ^ 3 - 84 * b) = 0 := by linarith [eq4, eq5]
    have eq7 : (a - b) * (a ^ 2 + a * b + b ^ 2 - 84) = 0 := by 
      nlinarith 
    have ne1 : a - b ≠ 0 := by linarith 
    have eq8 : a ^ 2 + a * b + b ^ 2 - 84 = 0 := by 
      apply (mul_left_inj' ne1).mp 
      linarith 
    linarith 

  -- Subtract the second and the third root equation: (b^3 - 84 b) - (c^3 - 84 c) = 0
  have eq4 : b ^ 2 + b * c + c ^ 2 = 84 := by 
    have eq4 : b ^ 3 - 84 * b = M := h2 
    have eq5 : c ^ 3 - 84 * c = M := h3 
    have eq6 : b ^ 3 - 84 * b - (c ^ 3 - 84 * c) = 0 := by linarith [eq4, eq5]
    have eq7 : (b - c) * (b ^ 2 + b * c + c ^ 2 - 84) = 0 := by 
      nlinarith 
    have ne1 : b - c ≠ 0 := by linarith 
    have eq8 : b ^ 2 + b * c + c ^ 2 - 84 = 0 := by 
      apply (mul_left_inj' ne1).mp 
      linarith 
    linarith

  -- From eq3 and eq4, we can deduce a + b + c = 0
  have eq5 : (a - c) * (a + b + c) = 0 := by
    nlinarith [eq3, eq4]

  cases (mul_eq_zero.mp eq5) with
  | inl h8 =>
    nlinarith
  | inr h9 =>
    -- From h9: a + b + c = 0
    -- From h7: 3b = 2a + c
    -- Solving these together.
    have eq6 : a + b + c = 0 := by linarith 
    have eq7 : a = 4 * b := by
      nlinarith 
    have eq8 : c = -5 * b := by 
      nlinarith 
    have eq9 : b ^ 2 = 4 := by
      rw [show a = 4 * b by linarith] at eq3
      nlinarith 
    have eq10 : b = 2 ∨ b = -2 := by
      have h11 : b ^ 2 - 4 = 0 := by nlinarith 
      have h12 : (b - 2) * (b + 2) = 0 := by nlinarith 
      cases (mul_eq_zero.mp h12) with
      | inl h13 => 
        left 
        nlinarith 
      | inr h14 => 
        right 
        nlinarith 
    cases eq10 with
    | inl h11 =>
      -- contradiction with order
      nlinarith
    | inr h11 =>
      have eq14 : b = -2 := h11 
      nlinarith [h2, eq14]