import Mathlib

theorem algebra_94796 {F : ℕ → ℝ} (hF : ∀ n ≥ 1, F (n + 1) = (2 * F n + 1) / 2) (hF1 : F 1 = 2) :
    F 101 = 52 := by 
  have h : ∀ n, F (n + 1) = (n + 4) / 2 := by
    intro n
    induction n with
    | zero =>
      -- For the base case, prove that $F(1) = \frac{0 + 4}{2} = 2$, which matches hF1.
      simp [hF1]
      all_goals norm_num
    | succ n ih =>
      -- For the inductive step, we assume $F(n + 1) = \frac{n + 4}{2}$.
      -- We need to prove $F((n + 1) + 1) = \frac{(n + 1) + 4}{2} = \frac{n + 5}{2}$.
      have h1 := hF (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at h1 ⊢
      rw [h1]
      simp [ih]
      all_goals field_simp <;> ring
  have h100 := h 100
  norm_num at h100 ⊢
  linarith