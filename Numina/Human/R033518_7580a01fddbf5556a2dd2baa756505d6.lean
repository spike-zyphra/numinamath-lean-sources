import Mathlib

open Real Set
open scoped BigOperators

/- 4. Solve the inequality $4+x^{2}+2 x \sqrt{2-x^{2}}<8 \sqrt{2-x^{2}}+5 x$. (20 points) -/

theorem inequalities_260266 (x : ℝ) :
  4 + x^2 + 2 * x * sqrt (2 - x^2) < 8 * sqrt (2 - x^2) + 5 * x ∧ 0 ≤ 2 - x^2 ↔
  -1 < x ∧ x ≤ sqrt 2 := by

  constructor
  · intro h
    -- rewrite everything to one side
    obtain ⟨heq, hdef⟩ := h
    -- from hdef we can get x≤√2
    have hs:x≤√2 := by
      refine le_sqrt_of_sq_le ?_; linarith
    have h': 0 < 8 * √(2 - x ^ 2) + 5 * x - 4 - x ^ 2 - 2 * x * √(2 - x ^ 2) := by linarith
    -- we can factor the rhs
    conv_rhs at h' =>
      calc _
      _ = 2*(4 - x) * √(2 - x ^ 2) + (4-x)*(x-1) := by ring_nf
      _ = (4 - x) * (x-1 + 2*√(2 - x ^ 2)) := by ring_nf
    apply mul_pos_iff.mp at h'
    cases' h' with h' h'
    -- one side can be eliminated
    rotate_left
    exfalso
    have h'':=h'.left
    simp at hdef h''
    nlinarith
    -- now for the other side
    obtain ⟨_, hr⟩ := h'
    have hl': (1-x)/2 < √(2-x^2) := by linarith
    -- to be able to square both sides we need 1-x>0
    -- first two cases are boring
    cases' lt_trichotomy (1-x) 0 with h1 h1
    · exact ⟨by nlinarith, hs⟩
    cases' h1 with h1 h1
    · have hx:x=1 := by linarith
      rw [hx]; norm_num
    · apply (Real.lt_sqrt (by linarith)).mp at hl'
      ring_nf at hl'
      have h2: 0 < (2 - x^2 -(1 / 4 + x * (-1 / 2) + x ^ 2 * (1 / 4)))*4 := by linarith
      -- we end up with a quadratic that we factor
      conv_rhs at h2 =>
        calc (2 - x ^ 2 - (1 / 4 + x * (-1 / 2) + x ^ 2 * (1 / 4))) * 4
        _ = 7 + x * 2 - x ^ 2 * 5 := by ring_nf
        _ = -(5*x-7)*(x+1) := by ring_nf
      apply mul_pos_iff.mp at h2
      cases' h2 with h2 h2
      · constructor
        · linarith
        exact hs
      · constructor
        · linarith
        exact hs

  -- now for the other side, just go in reverse mostly, not much thinking needed
  intro ⟨hl, hr⟩
  constructor
  rotate_left
  · simp
    refine (Real.sq_le ?_).mpr ?_
    norm_num
    constructor
    · suffices -√2≤ -1 by linarith
      simp
    assumption
  suffices 0 < 8 * √(2 - x ^ 2) + 5 * x - 4 - x ^ 2 - 2 * x * √(2 - x ^ 2) by linarith
  conv_rhs =>
      calc _
      _ = 2*(4 - x) * √(2 - x ^ 2) + (4-x)*(x-1) := by ring_nf
      _ = (4 - x) * (x-1 + 2*√(2 - x ^ 2)) := by ring_nf
  apply mul_pos_iff.mpr
  left
  constructor
  suffices √2<2 by linarith
  refine (sqrt_lt' ?_).mpr ?_
  norm_num
  norm_num
  suffices (1-x)/2 < √(2-x^2) by linarith
  cases' lt_trichotomy (1-x) 0 with h1 h1
  · simp at h1
    suffices (1 - x) / 2 < 0 by
      apply lt_of_lt_of_le (b:=0) this
      exact sqrt_nonneg (2 - x ^ 2)
    linarith
  cases' h1 with h1 h1
  · have hx:x=1 := by linarith
    rw [hx]; norm_num
  simp at h1
  refine (lt_sqrt ?_).mpr ?_
  linarith
  ring_nf
  suffices 0 < (2 - x^2 -(1 / 4 + x * (-1 / 2) + x ^ 2 * (1 / 4)))*4 by linarith
  conv_rhs =>
    calc (2 - x ^ 2 - (1 / 4 + x * (-1 / 2) + x ^ 2 * (1 / 4))) * 4
    _ = 7 + x * 2 - x ^ 2 * 5 := by ring_nf
    _ = -(5*x-7)*(x+1) := by ring_nf
  apply mul_pos_iff.mpr
  left
  constructor
  linarith
  linarith