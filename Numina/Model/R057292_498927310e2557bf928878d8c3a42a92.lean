import Mathlib

theorem algebra_18816 (P : ℤ → ℤ) (hP : P = fun x => 2*x^4 + 4*x^3 - 5*x^2 + 2*x - 3) :
    P 1 = 0 ∧ P (-3) = 0 ∧ ∀ x, P x = 0 → x = 1 ∨ x = -3 := by
  constructor
  · -- Show that 1 is a root
    rw [hP]
    norm_num
  constructor
  · -- Show that -3 is a root
    rw [hP]
    norm_num
  · -- Now show that any root must be 1 or -3
    intro x hx
    rw [hP] at hx
    simp at hx
    have h1 : (x - 1) * (x + 3) * (2 * x^2 + 1) = 0 := by
      ring_nf at hx ⊢
      linarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case x - 1 = 0
      left
      linarith
    · -- Case x + 3 = 0
      right
      linarith
    · -- Case 2*x^2 + 1 = 0, which is impossible
      exfalso
      nlinarith [sq_nonneg (x : ℤ)]