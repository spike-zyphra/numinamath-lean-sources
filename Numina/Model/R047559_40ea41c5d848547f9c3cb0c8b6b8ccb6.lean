import Mathlib

theorem algebra_15629 : {c : ℝ | 0 < c ∧ ∃ x : ℝ, x^2 - 6 * x + c < 0} = Set.Ioo 0 9 := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- First, show that if 0 < c and ∃x, x^2 -6x + c <0, then 0 <c <9
    intro h
    rcases h with ⟨hc_pos, ⟨x, hx⟩⟩
    have h1 : c < 9 := by
      nlinarith [sq_nonneg (x - 3)]
    constructor
    . linarith
    . linarith
  · -- Now show that if c ∈ (0, 9), then 0 < c and ∃ x, x^2 -6 x +c <0
    rintro ⟨hc_pos, hc_lt⟩
    constructor
    . linarith
    . -- Show existence of x
      use 3 - Real.sqrt (9 - c)/2
      have h2 : (3 - Real.sqrt (9 - c)/2: ℝ) ^2 -6 * (3 - Real.sqrt (9 - c)/2 : ℝ) + c < 0 := by
        have h3 : 0 ≤ (9 - c : ℝ) := by linarith
        have h4 : (Real.sqrt (9 - c)) ^2 = 9 - c := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (9 - c), h4]
      linarith [h2]