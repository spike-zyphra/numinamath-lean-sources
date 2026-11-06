import Mathlib

theorem algebra_175346 (n : ℕ) (hn : n > 0) (x : Fin n → ℝ)
    (h1 : ∑ i : Fin n, x i = 2.3 * n) (h2 : ∑ i : Fin n, (x i)^2 = 8.7 * n) :
    ∃ a σ : ℝ, a = 2.3 ∧ σ^2 = 3.41 := by
  exact ⟨2.3, Real.sqrt (3.41 : ℝ), by norm_num, by
    have h3 : (Real.sqrt (3.41 : ℝ)) ^ 2 = 3.41 := Real.sq_sqrt (by norm_num)
    linarith [h3]
⟩