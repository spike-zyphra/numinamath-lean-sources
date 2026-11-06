import Mathlib

theorem algebra_21106 :
    {r | ∃ a b c : ℝ, a * b + a * c + b * c = 0 ∧ (a + b + c + 1) ^ 2 = a * b * c ∧ (a * b - c) * (a * c - b) * (b * c - a) = r} = {0} := by 
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume r in left side set, prove r = 0
    rintro ⟨a, b, c, h1, h2, h3⟩
    nlinarith [sq_nonneg (a * b - c), sq_nonneg (a * c - b), sq_nonneg (b * c - a), sq_nonneg (a + b + c + 1), sq_nonneg (a + b + c), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (a * c)]
  · -- Assume r = 0 in right side set, prove r in left side set.
    intro h
    rw [h]
    use 0, 0, -1
    constructor
    · -- Show that a * b + a * c + b * c = 0
      norm_num
    constructor
    · -- Show that (a + b + c + 1) ^ 2 = a * b * c
      norm_num 
    · -- Show that (a * b - c) * (a * c - b) * (b * c - a) = 0
      norm_num