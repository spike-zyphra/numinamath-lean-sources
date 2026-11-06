import Mathlib



theorem Algebra_9432 (f : ℝ → ℝ) (hf : f = fun (x : ℝ) => - (Real.sin x) ^ 3 - 2 * Real.sin x) :
  IsLeast (Set.range f) (-3) := by

  have h1 : ∀ x, f x = - (Real.sin x) ^ 3 - 2 * Real.sin x := by
    intro x
    rw [hf]

  constructor
  · -- First part: show that -3 is in the range of f
    use Real.pi / 2
    rw [h1]
    have hsin : Real.sin (Real.pi / 2) = 1 := by
      exact Real.sin_pi_div_two
    rw [hsin]
    all_goals norm_num

  · -- Second part: show that -3 is the smallest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h2 : - (Real.sin x) ^ 3 - 2 * Real.sin x ≥ -3 := by
      nlinarith [sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1), sq_nonneg (Real.sin x ^ 2 - 1), Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x), Real.sin_le_one x, Real.neg_one_le_sin x]
    linarith