import Mathlib

theorem algebra_10287 : (∑ᶠ x ∈ {x : ℝ | (2 * x ^ 2 + 1) = 19}, x) / {x : ℝ | (2 * x ^ 2 + 1) = 19}.ncard = 0 := by
  have h1 : {x : ℝ | (2 * x ^ 2 + 1) = 19} = {3, -3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume $2 * x^2 + 1 = 19$, prove $x = 3 \lor x = -3$
      intro h
      have h2 : 2 * x^2 + 1 = 19 := by linarith
      have h3 : 2 * x^2 = 18 := by linarith
      have h4 : x^2 = 9 := by linarith
      have h5 : x = 3 ∨ x = -3 := by
        have h6 : x^2 - 9 = 0 := by linarith
        have h7 : (x - 3) * (x + 3) = 0 := by 
          linarith 
        cases (mul_eq_zero.mp h7) with 
        | inl h8 =>
          left 
          linarith
        | inr h9 =>
          right 
          linarith 
      exact h5 
    · -- Assume $x = 3 \lor x = -3$, prove $2 * x^2 + 1 = 19$
      rintro (h | h)
      · -- x = 3
        rw [h]
        norm_num
      · -- x = -3
        rw [h]
        norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  norm_num
  all_goals norm_num