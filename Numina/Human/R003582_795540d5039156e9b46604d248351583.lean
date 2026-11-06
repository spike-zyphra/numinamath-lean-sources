import Mathlib

/- For given values of $a, b, c$ and $d$, it turned out that the graphs of the functions $y=2 a+\frac{1}{x-b}$ and $y=2 c+\frac{1}{x-d}$ have exactly one common point. Prove that the graphs of the functions $y=2 b+\frac{1}{x-a}$ and $y=2 d+\frac{1}{x-c}$ also have exactly one common point. -/

-- lemma that the unique solution of existence in problem is equivalent to (a - c) * (b - d) = 0
lemma l_uniq_soln {a b c d : ℝ} : (∃! x, x - b ≠ 0 ∧ x - d ≠ 0 ∧ 2 * a + 1 / (x - b) = 2 * c + 1 / (x - d))
    ↔ (a - c) * (b - d) = 2 := by
  constructor
  -- if x is unique solution, then (b + d - x) is another solution
  . rintro ⟨x, ⟨hbx, hdx, hx⟩, hx'⟩
    specialize hx' (b + d - x)
    simp at hx'
    ring_nf at hx'
    rw [← neg_ne_zero] at hbx hdx
    ring_nf at hbx hdx hx' hx
    simp [hbx, hdx] at hx'
    have h1 {p q : ℝ} : (-p + q)⁻¹ = - (p - q)⁻¹ := by
      rw [neg_inv]
      congr
      ring
    rw [h1, h1] at hx'
    specialize hx' (by linarith)
    -- so x = b + d - x i.e. x = (b + d - 2)
    have h2 : x = (b + d) / 2 := by linarith
    -- now plugging int the equation we get (a - c) = 2 / (b - d) and result is true
    rw [h2] at hx hbx
    conv_lhs at hx => arg 2; arg 1; equals (d - b)/2 => ring
    rw [inv_div] at hx
    conv_rhs at hx => arg 2; arg 1; equals (b - d)/2 => ring
    rw [inv_div] at hx
    rw [← neg_sub, div_neg_eq_neg_div] at hx
    replace hx : (a - c) = 2 / (b - d) := by linarith
    have : b - d ≠ 0 := by
      ring_nf at hbx
      by_contra h
      apply hbx (by linarith)
    field_simp at hx
    assumption
  -- if (a - c) * (b - d) = 0 we'll show (b + d) / 2 is the unique solution
  . rintro h
    use ((b + d) / 2)
    simp
    -- first of all b - d ≠ 0 as it is factor of 2
    have hbd : b - d ≠ 0 := by
      by_contra h'
      rw [h'] at h
      simp at h
    and_intros
    -- the non equality conditions are obvious
    . ring_nf
      by_contra h'
      apply hbd (by linarith)
    . ring_nf
      by_contra h'
      apply hbd (by linarith)
    -- the equation is satisfied as it becmes equivalent to (a - c) * (b - d) = 2
    . conv_lhs => arg 2; arg 1; equals (d - b)/2 => ring
      rw [inv_div]
      conv_rhs => arg 2; arg 1; equals (b - d)/2 => ring
      rw [inv_div, ← neg_sub, div_neg_eq_neg_div]
      suffices (a - c) = 2 / (b - d) by linarith
      field_simp
      exact h
    -- if y is another solution thenn 4 / (b - d) = (y - d)⁻¹ - (y - b)⁻¹, multiplying this out, we get (2*y - b - d) = 0, so y = (b + d)/2
    . rintro y hy1 hy2 hy
      replace hy : 2 * (a - c) = (y - d)⁻¹ - (y - b)⁻¹ := by linarith
      conv_lhs at hy => arg 2; equals 2 * (b - d)⁻¹ => field_simp; assumption
      field_simp at hy
      replace hy : (2 * y - b - d)^2 = 0 := by linarith
      simp at hy
      linarith

theorem algebra_198625 {a b c d : ℝ}
    (h : ∃! x, x - b ≠ 0 ∧ x - d ≠ 0 ∧ 2 * a + 1 / (x - b) = 2 * c + 1 / (x - d)) :
    ∃! x, x - a ≠ 0 ∧ x - c ≠ 0 ∧ 2 * b + 1 / (x - a) = 2 * d + 1 / (x - c) := by
  -- just use lemma to turn both hypothesis and goal to algebraic equaiton which are equivalent
  rw [l_uniq_soln] at h ⊢
  linarith