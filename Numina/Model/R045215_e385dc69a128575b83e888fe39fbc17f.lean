import Mathlib

theorem algebra_70487 :
    IsLeast {d | ∃(a b c e : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ 
        ∀(x : ℝ), (x + a) * (x + b) * (x + c) = x^3 + 3 * d * x^2 + 3 * x + e^3} 1 := by
  constructor
  · -- Show 1 is in the set.
    use 1, 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    intro x
    ring
  · -- Show that 1 is the least element in the set.
    intro d hd
    rcases hd with ⟨a, b, c, e, ha, hb, hc, hd, he, h⟩
    have eq1 := h 0
    have eq2 := h 1
    have eq3 := h (-1)
    have eq4 := h 2
    have h4 : a * b + a * c + b * c = 3 := by
      ring_nf at eq1 eq2 eq3 eq4
      nlinarith
    have h5 : a + b + c = 3 * d := by
      ring_nf at eq1 eq2 eq3 eq4
      nlinarith
    have h6 : d ≥ 1 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    linarith