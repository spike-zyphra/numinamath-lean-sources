import Mathlib

theorem algebra_258802 {a : ℕ → ℝ} (ha : a 1 > 0) (h : ∀ n, a (n + 1) = (5 * a n - 8) / (a n - 1)) :
    (∀ n, 0 < n → a n > 3) ↔ 3 < a 1 := by
  constructor
  · -- Forward direction: if ∀ n > 0, a n > 3 then 3 < a 1
    intro h1
    have h2 := h1 1 (by norm_num)
    linarith
  · -- Backward direction: if 3 < a 1 then ∀ n > 0, a n > 3
    intro h1
    have h2 : ∀ (n : ℕ), 0 < n → a n > 3 := by
      intro n hn
      induction n with
      | zero => 
        exfalso
        linarith
      | succ n ih =>
        cases n with
        | zero => 
          -- Base case where n = 1
          exact h1
        | succ n => 
          -- Inductive step
          have h3 : a (n + 1) > 3 := by 
            apply ih
            linarith
          -- We need to show a (n + 2) > 3
          have eq1 : a (n + 2) = (5 * a (n + 1) - 8) / (a (n + 1) - 1) := by
            specialize h (n + 1)
            simpa using h
          rw [eq1]
          have h4 : a (n + 1) - 1 > 0 := by
            nlinarith
          have h5 : (5 * a (n + 1) - 8) / (a (n + 1) - 1) > 3 := by
            apply (lt_div_iff₀ (by linarith)).mpr
            nlinarith
          linarith
    simpa using h2
    all_goals try linarith