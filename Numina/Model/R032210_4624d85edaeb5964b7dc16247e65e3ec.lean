import Mathlib

theorem algebra_276104 :
  {x : ℝ | x > 0 ∧ (x - (x - 4)^3/x^2) = (x - 4)^3/x^2 + 2.5} = {16} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Proof of (LHS => RHS).
    intro h
    rcases h with ⟨hx, heq⟩
    have hx1 : x ≠ 0 := by linarith
    field_simp [hx1] at heq
    ring_nf at heq
    have h1 : (x - 16) * (x ^ 2 - 5.5 * x + 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where x - 16 = 0
      linarith
    · -- Case where x^2 - 5.5 x + 8 = 0
      exfalso
      have h2 : x ^ 2 - 5.5 * x + 8 = 0 := by
        nlinarith
      have h8 : (x - 2.75 : ℝ) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
  · -- Proof of (RHS => LHS).
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num