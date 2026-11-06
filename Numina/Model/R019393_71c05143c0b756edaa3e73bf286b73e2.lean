import Mathlib

theorem algebra_36467 (f : ℝ → ℝ) (hf : f = fun x => 4*x^4 - 3*x^2 + 7*x - 3) :
    ∑ᶠ x ∈ {x | f x = 0}, x = -1 := by
  have h1 : {x : ℝ | f x = 0} = {1 / 2, -3 / 2} := by
    ext x
    simp [hf]
    constructor
    · -- Assume that x is a root
      intro h
      have h_eq : 4 * x ^ 4 - 3 * x ^ 2 + 7 * x - 3 = 0 := by
        simpa using h
      have h2 : (x - 1 / 2) * (x + 3 / 2) * (4 * x ^ 2 - 4 * x + 4) = 0 := by
        nlinarith [sq_nonneg (x), sq_nonneg (x - 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (4 * x ^ 2 - 4 * x + 2)]
      cases' (mul_eq_zero.mp h2) with h2h h2q
      cases' (mul_eq_zero.mp h2h) with h2h1 h2h2
      · -- First factor x - 1/2 = 0
        left
        linarith
      · -- Second factor x + 3/2 =0
        right
        linarith
      · -- Last factor 4x^2 -4x +4=0
        have h3 : 4 * x ^ 2 - 4 * x + 4 > (0 : ℝ) := by
          nlinarith [sq_nonneg (x - 1 / 2)]
        have h4 : 4 * x ^ 2 - 4 * x + 4 = 0 := by linarith
        nlinarith
    · -- Show x in {1/2, -3/2} satisfies polynomial
      rintro (rfl | rfl)
      · -- Check x = 1/2
        norm_num
      · -- Check x = -3/2
        norm_num
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num