import Mathlib

theorem algebra_186882 : IsGreatest (Set.image (fun x => 3 * Real.sin x + 4 * Real.cos x) (Set.univ : Set ℝ)) 5 := by
  constructor
  · -- First, we show that 5 belongs to the image of f
    use Real.arcsin (3 / 5)
    have h1 : Real.sin (Real.arcsin (3 / 5)) = 3 / 5 := by
      apply Real.sin_arcsin
      all_goals norm_num
    have h2 : Real.cos (Real.arcsin (3 / 5)) = 4 / 5 := by
      have h2 : Real.cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by
        rw [Real.cos_arcsin]
        all_goals norm_num
      rw [h2]
      have h3 : Real.sqrt (1 - (3 / 5) ^ 2) = 4 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact h3
    simp [h1, h2]
    all_goals norm_num
  · -- Next, we show that 5 is an upper bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    simp at hx
    have h1 : (3 * Real.sin x + 4 * Real.cos x) ≤ 5 := by
      nlinarith [sq_nonneg (3 * Real.cos x - 4 * Real.sin x), sq_nonneg (Real.sin x - 3 / 5), sq_nonneg (Real.cos x - 4 / 5), Real.sin_sq_add_cos_sq x, sq_nonneg (3 ^ 2 + 4 ^ 2 - 25), sq_nonneg (Real.sin x * 4 - Real.cos x * 3), sq_nonneg (Real.sin x ^ 2 + Real.cos x ^ 2 - 1)]
    linarith [hx, h1]