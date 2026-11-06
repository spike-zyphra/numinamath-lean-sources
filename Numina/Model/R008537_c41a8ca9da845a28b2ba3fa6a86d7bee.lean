import Mathlib
theorem algebra_607974 (P : ℝ → ℝ) (hP : P = fun x => x ^ 8 - x ^ 7 + 2 * x ^ 6 - 2 * x ^ 5 + 3 * x ^ 4 - 3 * x ^ 3 + 4 * x ^ 2 - 4 * x + 5 / 2) : ¬∃ x : ℝ, P x = 0:= by
    intro h
    rcases h with ⟨x₀, hx₀⟩
    simp [hP] at hx₀
    nlinarith [sq_nonneg (x₀ ^ 4), sq_nonneg (x₀ ^ 3 - 1 / 2), sq_nonneg (x₀ ^ 2 - 1 / 2), sq_nonneg (x₀ - 1 / 2), sq_nonneg (x₀ ^ 4 - x₀ ^ 3 / 2), sq_nonneg (x₀ ^ 2 - x₀ / 2), sq_nonneg (x₀ ^ 4 - 1 / 2), sq_nonneg (x₀ ^ 2 - 1 / 2), sq_nonneg (x₀ - 1 / 2)]