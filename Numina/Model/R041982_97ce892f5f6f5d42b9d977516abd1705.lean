import Mathlib

theorem algebra_188770 {x : ℕ → ℝ} (hx1 : x 1 > 3)
    (hxn : ∀ n ≥ 2, x n = (3 * (x (n - 1))^2 - x (n - 1))/(4 * (x (n - 1) - 1))) :
    ∀ n ≥ 1, 3 < x (n + 1) ∧ x (n + 1) < x n := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      have h2 : 3 < x 2 := by
        have h10 : x 2 = (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) := by
          specialize hxn 2 (by norm_num)
          simpa using hxn
        rw [h10]
        have h11 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) > 3 := by
          have h12 : 4 * (x 1 - 1) > 0 := by
            nlinarith
          apply (lt_div_iff' h12).mpr
          nlinarith [sq_nonneg (x 1 - 3), sq_nonneg (x 1 - 4 / 3), show x 1 - 3 > 0 by linarith]
        linarith
      have h2' : x 2 < x 1 := by
        have h10 : x 2 = (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) := by
          specialize hxn 2 (by norm_num)
          simpa using hxn
        rw [h10]
        have h11 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) < x 1 := by
          have h12 : 4 * (x 1 - 1) > 0 := by
            nlinarith
          apply (div_lt_iff' h12).mpr
          nlinarith [sq_nonneg (x 1 - 3), sq_nonneg (x 1 - 0), show x 1 - 3 > 0 by linarith]
        linarith
      constructor
      · -- Show that 3 < x 2
        linarith [h2]
      · -- Show that x 2 < x 1
        linarith [h2']
    | succ n =>
      have h1 := ih (by linarith)
      have h2 : 3 < x (n + 1 + 1) := h1.1
      have h3 : x (n + 1 + 1) < x (n + 1) := h1.2
      have h10 : x (n + 1 + 1 + 1) = (3 * (x (n + 1 + 1))^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) := by
        specialize hxn (n + 1 + 1 + 1) (by linarith)
        simpa using hxn
      have h11 : 3 < x (n + 1 + 1 + 1) := by
        rw [h10]
        have h12 : 0 < x (n + 1 + 1) - 1 := by linarith
        have h13 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) > 3 := by
          have h14 : 4 * (x (n + 1 + 1) - 1) > 0 := by
            nlinarith
          apply (lt_div_iff' h14).mpr
          nlinarith [sq_nonneg (x (n + 1 + 1) - 3), sq_nonneg (x (n + 1 + 1) - 4 / 3), show x (n + 1 + 1) - 3 > 0 by linarith]
        linarith
      have h14 : x (n + 1 + 1 + 1) < x (n + 1 + 1) := by
        rw [h10]
        have h15 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) < x (n + 1 + 1) := by
          have h16 : 4 * (x (n + 1 + 1) - 1) > 0 := by
            nlinarith
          apply (div_lt_iff' h16).mpr
          nlinarith [sq_nonneg (x (n + 1 + 1) - 3), sq_nonneg (x (n + 1 + 1) - 0), show x (n + 1 + 1) - 3 > 0 by linarith]
        linarith
      constructor
      · -- Show that 3 < x (n + 1 + 1 + 1)
        linarith [h11]
      · -- Show that x (n + 1 + 1 + 1) < x (n + 1 + 1)
        linarith [h14]