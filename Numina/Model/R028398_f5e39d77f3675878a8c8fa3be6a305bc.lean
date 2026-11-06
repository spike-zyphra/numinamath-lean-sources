import Mathlib

theorem number_theory_109171 (f : ℕ → ℕ)
    (h₀ : ∀ n, f n = if n ≥ 1000 then n - 3 else f (f (n + 7))) :
    f 90 = 999 := by
  set_option maxRecDepth 100000 in 
  simp [h₀]
  <;> omega