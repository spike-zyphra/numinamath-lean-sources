import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197908 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2*b + c + 2*d - a*b - b*c - c*d - d*a ∧
    a ∈ Icc (-13.5) 13.5 ∧ b ∈ Icc (-13.5) 13.5 ∧ c ∈ Icc (-13.5) 13.5 ∧ d ∈ Icc (-13.5) 13.5} 756 := by
  constructor
  · -- Show that 756 is in the set
    use -13.5, 13.5, -13.5, 13.5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 756 is the greatest value
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    -- simplify the equations
    ring_nf at h_eq
    nlinarith [sq_nonneg (a + 13.5 : ℝ), sq_nonneg (b - 13.5 : ℝ), sq_nonneg (c + 13.5 : ℝ), sq_nonneg (d - 13.5 : ℝ)]