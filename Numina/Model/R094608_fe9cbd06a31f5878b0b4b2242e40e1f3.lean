import Mathlib

def Δ (u : ℕ → ℝ) (n : ℕ) := u (n + 1) - u n

theorem algebra_281656 {u : ℕ → ℝ} (hu : ∀ n, u n = n ^ 3 + n) :
    (∀ n, Δ^[4] u n = 0) ∧ ¬(∀ n, Δ^[3] u n = 0) := by
  -- We will first prove that for $u_n = n^3 + n$, the 4th difference is zero
  constructor
  · -- We want to show that $\Delta^4 u_n = 0$ for all $n$
    intro n
    simp [Δ, hu]
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  · -- Now we need to show that it's not true that $\Delta^3 u_n = 0$ for all $n$
    intro h
    -- Assume $\forall n, \Delta^3 u_n = 0$
    have h0 := h 0
    norm_num [Δ, hu] at h0
    all_goals norm_num at h0
    all_goals linarith