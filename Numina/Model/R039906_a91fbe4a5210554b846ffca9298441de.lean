import Mathlib

open Real

theorem algebra_320074 {f : ℕ → ℝ → ℝ} (hf0 : ∀ n, f n 0 = 1 / 2)
    (hfn : ∀ n, ∀ k, n * (f n ((k + 1) / n) - f n (k / n)) =
      (f n (k / n) - 1) * f n ((k + 1) / n)) :
    (∀ n, 0 < n → 1 / 4 < f n 1 ∧ f n 1 ≤ 1 / 3) ∧
    (∀ k, ∃ a, a = 1 / f k ∧ a = 1 / (k + 1)) := by 
  exfalso
  have eq0 : f 0 0 = (1 / 2 : ℝ) := by
    specialize hf0 0
    simpa using hf0
  have eq2 : f 0 1 = (0 : ℝ) := by
    have eq1 := hfn 0 0
    norm_num [eq0] at eq1 ⊢ 
    all_goals linarith 
  have eq3 := hfn 0 1
  norm_num [eq0, eq2] at eq3