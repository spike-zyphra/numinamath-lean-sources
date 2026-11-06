import Mathlib

open Real Set

/-Let $a$ and $b$ be nonzero real numbers.  Find the minimum value of
\[a^2 + b^2 + \frac{1}{a^2} + \frac{b}{a}.\]-/
theorem algebra_13384 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a^2 + b^2 + 1 / a^2 + b / a ≥ sqrt 3 ∧
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a^2 + b^2 + 1 / a^2 + b / a = sqrt 3 := by
  -- We complete the square with respect to the terms $b^2$ and $\frac{b}{a},$ to get
  -- b^2 + \frac{b}{a} = \left( b + \frac{1}{2a} \right)^2 - \frac{1}{4a^2}.
  have h1 : b^2 + b / a = (b + 1 / (2 * a))^2 - 1 / (4 * a^2) := by ring_nf

  constructor
  . -- a^2 + b^2 + 1 / a^2 + b / a ≥ sqrt 3
    apply le_trans
    case left.b => exact a^2 + 3 / (4 * a^2)
    -- now, to prove √3 ≤ a ^ 2 + 3 / (4 * a ^ 2)
    have : 3 / (4 * a ^ 2) = (√3 / (2 * a))^2 := by
      ring_nf
      rw [Real.sq_sqrt]
      ring_nf
      linarith
    rw [this]
    have : √3 = 2 * a * (√3 / (2 * a)) := by
      ring_nf
      rw [←one_div, mul_div, mul_one, mul_div_right_comm, div_self, one_mul]
      exact ha
    rw (config := { occs := .pos [1]}) [this]
    -- 2xy ≤ x^2 + y^2
    apply two_mul_le_add_sq
    have : a^2 + 3 / (4 * a^2) = (a^2 + 1 / a^2) + (-1 / (4 * a^2)) := by ring_nf
    rw [this]
    have : a ^ 2 + b ^ 2 + 1 / a ^ 2 + b / a = (a ^ 2 + 1 / a ^ 2) + (b ^ 2 + b / a) := by ring_nf
    rw [this]
    apply add_le_add_three
    exact Preorder.le_refl (a ^ 2)
    exact Preorder.le_refl (1 / a ^ 2)
    rw [h1]
    apply le_sub_iff_add_le.mpr
    rw [←neg_one_mul, ←mul_div, neg_one_mul, neg_add_cancel]
    apply pow_two_nonneg

  . --  ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a^2 + b^2 + 1 / a^2 + b / a = sqrt 3
    have : ∃(a : ℝ), a > 0 ∧ a^4 = 3 / 4 := by
      use √(√(3 / 4))
      have : 4 = 2 + 2 := by ring
      rw [this, pow_add, Real.sq_sqrt, ←pow_two, Real.sq_sqrt]
      constructor
      . -- a > 0
        apply sqrt_pos_of_pos
        apply sqrt_pos_of_pos
        linarith
      linarith
      linarith
      exact sqrt_nonneg (3 / 4)
    rcases this with ⟨a, ⟨agt0, ha⟩⟩
    use a
    use (-1/(2 * a))
    constructor
    . -- a ≠ 0
      intro ha'
      rw [ha'] at ha
      simp at ha
      linarith
    constructor
    . -- b ≠ 0
      intro hb
      simp at hb
      rw [hb] at ha
      linarith
    -- a^2 + b^2 + 1 / a^2 + b / a = sqrt 3
    ring_nf
    have ha' : a^2 = √(3 / 4) := by
      have : 4  = 2 + 2 := by ring
      rw [ha.symm, this, pow_add, Real.sqrt_mul, Real.sqrt_sq, ←pow_two]
      exact agt0.le
      apply pow_two_nonneg

    -- a ^ 2 + a⁻¹ ^ 2 * (3 / 4) = √3
    rw [←one_div, div_pow, ha']
    field_simp
    rw [←mul_assoc, Real.mul_self_sqrt (by linarith), ←mul_assoc, mul_comm (√4)]
    rw [mul_assoc, Real.mul_self_sqrt (by linarith), ←mul_assoc, mul_comm (√3)]
    rw [mul_assoc (√4), Real.mul_self_sqrt (by linarith)]
    have : √4 = 2 := by
      have : (4 : ℝ) = 2 ^ 2 := by ring
      rw [this, Real.sqrt_sq (by linarith)]
    rw [this]
    linarith
