import Mathlib

theorem algebra_152554 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b)
    (h : ∀ x, f (f x) = x) :
    (∀ x, f x = x) ∨ (∀ x, f x = -x + b) := by
  have eq1 := h 0
  rw [hf, hf] at eq1
  have eq2 := h 1
  rw [hf, hf] at eq2
  have eq1' : b * (a + 1) = 0 := by
    linarith 
  have eq3 : a^2 + a * b + b = 1 := by 
    nlinarith 
  cases (mul_eq_zero.mp eq1') with
  | inl hb0 =>
    have ha2 : a^2 = 1 := by
      nlinarith [eq3]
    have ha : a = 1 ∨ a = -1 := by
      rw [sq_eq_one_iff] at ha2
      exact ha2
    cases ha with
    | inl ha1 =>
      left
      intro x
      rw [hf]
      rw [ha1, hb0]
      ring
    | inr ha2 =>
      right
      intro x
      rw [hf]
      rw [ha2, hb0]
      ring
  | inr ha1 =>
    have ha2 : a = -1 := by linarith 
    right
    intro x
    rw [hf]
    rw [ha2]
    ring