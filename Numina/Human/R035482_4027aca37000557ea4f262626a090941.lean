import Mathlib

open Real

theorem inequalities_79687 {n : ℕ} (hn : 1 < n) (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hxn : x n ≤ 0) :
    (∑ i : Fin n, (x i) ^ ((i.1 + 1) / 2)) = n * (x n) ^ ((1 : ℝ) / 2) ∧
    (∑ i : Fin n, x i) / n = x n ↔ ∀ i, x i = 1 := by
        constructor
        · -- Forward direction: assuming the conditions hold
            intro h
            rcases h with ⟨h1, h2⟩
            have h3 : x n ≤ 0 := hxn
            have h4 := hx n
            linarith
        · -- Backward direction: assuming all x_i = 1, prove the conditions hold
            intro h
            have h1 := h n
            have h2 : x n ≤ 0 := hxn
            have h3 : x n = 1 := by
                simpa using h1
            linarith