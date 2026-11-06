import Mathlib

theorem algebra_186258 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + x + 1) :
    ¬∃ x, f x = 0 := by
        intro h
        rcases h with ⟨x , hx⟩
        rw [hf] at hx
        simp at hx
        have h1 : (x + 1 / 2) ^ 2 ≥ 0 := by
            apply sq_nonneg
        have h2 : x ^ 2 + x + 1 > (0 : ℝ) := by
            nlinarith [h1]
        linarith