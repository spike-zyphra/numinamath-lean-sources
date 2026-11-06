import Mathlib

theorem algebra_184541 {p q : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q)
    (hroots : ∃ x1 x2, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 ∧ |x2 - x1| = 7)
    (hS : f 0 = 8) :
    p = -9 ∧ q = 8 ∨ p = 9 ∧ q = 8 := by
  have hq: q = 8 := by
    rw [hf] at hS
    simp at hS
    linarith
  rw [hf] at hroots
  rcases hroots with ⟨x1, x2, hx1x2, hx1, hx2, hdist⟩
  simp [hq] at hx1 hx2
  have eq1 : x1 ^ 2 + p * x1 + 8 = 0 := by linarith
  have eq2 : x2 ^ 2 + p * x2 + 8 = 0 := by linarith
  have eq3 : (x1 ^ 2 + p * x1 + 8) - (x2 ^ 2 + p * x2 + 8) = 0 := by
    linarith
  have eq4 : x1 ^ 2 - x2 ^ 2 + p * (x1 - x2) = 0 := by
    linarith [eq3]
  have eq5 : (x1 - x2) * (x1 + x2 + p) = 0 := by
    linarith [eq4]
  cases (mul_eq_zero.mp eq5) with
  | inl h =>
    exfalso
    exact hx1x2 (by linarith)
  | inr h =>
    have hsum : x1 + x2 = -p := by linarith
    have eq6 : (x2 - x1) ^ 2 = 49 := by 
      cases eq_or_eq_neg_of_abs_eq hdist with
      | inl h7 =>
        have h7' : x2 - x1 = 7 := by linarith
        nlinarith [h7']
      | inr h7 =>
        have h7' : x2 - x1 = -7 := by linarith
        nlinarith [h7']
    have heq10 : x1 * x2 = 8 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx1x2)]
    have hp : p = 9 ∨ p = -9 := by
      have eq7 : x1 + x2 = -p := hsum
      -- Now using the relation between the roots:
      -- (x2 - x1)^2 = (x1 + x2)^2 - 4x1x2 
      -- 49 = (-p)^2 - 4 * 8
      -- 49 = p^2 - 32
      -- p^2 = 81
      -- p = ±9
      have eq8 : (x2 - x1) ^ 2 = (x1 + x2)^2 - 4 * (x1 * x2) := by
        nlinarith
      rw [eq7, heq10] at eq8
      have eq9 : (x2 - x1) ^ 2 = 49 := eq6
      have eq10 : (-p)^2 - 4 * (8) = 49 := by nlinarith [eq8, eq9]
      have eq11 : p^2 = 81 := by
        nlinarith [eq10]
      have eq12 : p^2 - 81 = 0 := by
        linarith [eq11]
      have eq13 : (p - 9) * (p + 9) = 0 := by
        nlinarith [eq12]
      cases (mul_eq_zero.mp eq13) with
      | inl h9 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    cases hp with
    | inl hp9 =>
      right
      constructor
      · linarith
      · linarith [hq]
    | inr hp9 =>
      left
      constructor
      · linarith
      · linarith [hq]