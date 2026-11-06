import Mathlib

open Real Set

theorem algebra_267494 {f : ℝ → ℝ} (hf : f = fun x => x^2 + 2 / (1 + 2 * x^2)) :
    IsLeast (range f) (3 / 2) ∧ ∃ x, f x = 3 / 2 := by
  constructor
  · -- Prove that 3/2 is the least element in the range of f
    constructor
    · -- Show 3/2 is in the range of f
      use Real.sqrt (1 / 2)
      have h1 : f (Real.sqrt (1 / 2)) = 3 / 2 := by
        rw [hf]
        have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
        simp [h2]
        <;> field_simp <;> norm_num
      linarith [h1]
    · -- Show 3/2 is a lower bound
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [hf] at hx
      simp at hx ⊢
      have h1 : x ^ 2 ≥ 0 := by
        exact sq_nonneg x
      have h2 : 1 + 2 * x ^ 2 > 0 := by
        nlinarith
      have h3 : x ^ 2 + 2 / (1 + 2 * x ^ 2) ≥ 3 / 2 := by
        have pos1 : 1 + 2 * x ^ 2 > 0 := by nlinarith [sq_nonneg x]
        have h4 : x ^ 2 + 2 / (1 + 2 * x ^ 2) - 3 / 2 ≥ 0 := by
          have h11 : (x ^ 2 + 2 / (1 + 2 * x ^ 2) - 3 / 2) = (2 * x ^ 2 * (1 + 2 * x ^ 2) + 2 * 2 - 3 * (1 + 2 * x ^ 2)) / (2 * (1 + 2 * x ^ 2)) := by
            field_simp
            ring
          rw [h11]
          apply div_nonneg
          nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
          positivity
        linarith
      linarith [h3, hx]
  · -- Show existence of x such that f(x) = 3/2
    use Real.sqrt (1 / 2)
    have h1 : f (Real.sqrt (1 / 2)) = 3 / 2 := by
      rw [hf]
      have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
      simp [h2]
      <;> field_simp <;> norm_num
    linarith [h1]