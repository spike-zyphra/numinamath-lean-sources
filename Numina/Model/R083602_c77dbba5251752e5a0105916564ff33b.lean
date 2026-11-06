import Mathlib

theorem algebra_303249 {a : ℕ → ℝ} (ha1 : a 1 = 5)
    (han : ∀ n ≥ 1, a (n + 1) = ((a n)^2 + 8 * a n + 16) / (4 * a n)) :
    ∀ n ≥ 1, a n ≥ 4 := by
  intro n hn
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 : a (n + 1 + 1) = ((a (n + 1))^2 + 8 * a (n + 1) + 16) / (4 * a (n + 1)) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      have h2 : a (n + 1) ≥ 4 := ih (by linarith)
      have h3 : a (n + 1 + 1) ≥ 4 := by
        rw [h1]
        have h4 : a (n + 1) > 0 := by linarith [h2]
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (a (n + 1) - 4)]
      exact h3