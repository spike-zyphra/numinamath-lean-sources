import Mathlib

theorem number_theory_251632 (f : ℕ → ℕ)
    (h₀ : ∀ n, f n = if n ≥ 1000 then n - 3 else f (f (n + 7))) :
    f 90 = 999 := by
  set_option maxRecDepth 10000 in
  simp [h₀]
  <;> omega