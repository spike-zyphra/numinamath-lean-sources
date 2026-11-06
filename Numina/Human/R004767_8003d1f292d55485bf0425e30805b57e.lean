import Mathlib

open Real

theorem algebra_319216 (f : ℕ → ℝ) (hf : ∀ x, f x = 0.2 * x + 18.5) :
    ¬∃ x, x ≤ 6 ∧ f x = 0.2 * x + 18.7 := by
        intro h
        rcases h with ⟨x, hx1, hx2⟩
        have hfx : f x = 0.2 * x + 18.5 := hf x
        rw [hfx] at hx2
        norm_num at hx2