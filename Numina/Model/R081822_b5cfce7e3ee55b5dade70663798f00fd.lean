import Mathlib

open Real

theorem calculus_309382 (f : ℝ → ℝ) (hf : f = fun x => sqrt x / (x^2 + x + 4)) :
    IsGreatest (Set.image f (Set.Ioi 0)) (1 / 6) := by
  constructor
  · -- Show 1/6 is in the image of f over (0, ∞)
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show f(1) = 1/6
      rw [hf]
      have h1 : sqrt (1 : ℝ) = 1 := by simp
      norm_num [h1]
  · -- Show 1/6 is the greatest value
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx_pos : x > 0 := by
      simpa using hx
    rw [hf] at hfx
    have h_eq : y = Real.sqrt x / (x ^ 2 + x + 4) := by
      simp [hf] at hfx ⊢
      linarith
    have h1 : Real.sqrt x / (x ^ 2 + x + 4) ≤ 1 / 6 := by
      have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ x by linarith)
      have h3 : 0 < x ^ 2 + x + 4 := by
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1), show x > 0 by linarith]
      have h4 : Real.sqrt x ≥ 0 := by
        apply Real.sqrt_nonneg
      have h5 : Real.sqrt x * 6 ≤ x^2 + x + 4 := by
        nlinarith [sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt (show 0 ≤ x by linarith), sq_nonneg (x - 1)]
      have h6 : Real.sqrt x / (x^2 + x + 4) ≤ 1 / 6 := by
        apply (div_le_div_iff (by positivity) (by norm_num)).mpr
        nlinarith
      linarith
    linarith [h_eq, h1]