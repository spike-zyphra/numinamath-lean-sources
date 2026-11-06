import Mathlib

theorem number_theory_245072 {x1 x2 : ℕ} (hx1 : x1 = 98) (hx2 : x2 = 32) :
    x1 ≠ x2 ∧ ∃ A G : ℕ, A ∈ Finset.Icc 10 99 ∧ G ∈ Finset.Icc 10 99 ∧
      A = (x1 + x2) / 2 ∧ G = √(x1 * x2) ∧
      ∃ p q r s : ℕ, A = 10 * p + q ∧ G = 10 * r + s ∧
        p = s ∧ q = r := by
  constructor
  · -- Show x1 ≠ x2
    rw [hx1, hx2]
    all_goals
      norm_num
  · -- Show the existence of A and G
    use 65, 56
    constructor
    · -- A ∈ [10, 99]
      rw [Finset.mem_Icc]
      all_goals norm_num
    constructor
    · -- G ∈ [10, 99]
      rw [Finset.mem_Icc]
      all_goals norm_num
    constructor
    · -- A = (x1 + x2) / 2
      rw [hx1, hx2]
      all_goals norm_num
    constructor
    · -- G = √(x1 * x2)
      have h13 : (56 : ℝ) = √(x1 * x2 : ℝ) := by
        have h14 : (x1 * x2 : ℝ) = (3136 : ℝ) := by 
          rw [hx1, hx2]
          norm_num
        rw [h14]
        have h15 : Real.sqrt (3136 : ℝ) = (56 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h15]
      exact_mod_cast h13
    · -- Show the existence of p, q, r, s
      use 6, 5, 5, 6
      all_goals
        norm_num