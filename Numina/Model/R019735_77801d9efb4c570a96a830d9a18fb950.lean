import Mathlib


theorem algebra_106659 (x : ℕ → ℝ)
    (hx1 : x 1 = 1) (hx2 : x 2 = 2)
    (hxn : ∀ n ≥ 1, x (n + 2) = (x (n + 1))^2 / ⌊Real.sqrt (x n^2 + x (n + 1))⌋ - 1 / n) :
    ∀ n ≥ 1, x n = n := by
  intro n hn
  have h1 : ∀ (n : ℕ), x (n + 1) = (↑n + 1 : ℝ) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [hx1]
    | succ n =>
      cases n with
      | zero =>
        norm_num [hx2]
      | succ n =>
        have h3 := ih n (by linarith)
        have h4 := ih (n + 1) (by linarith)
        have eq2 : x (n + 1 + 2) = (x (n + 1 + 1))^2 / ⌊Real.sqrt (x (n + 1)^2 + x (n + 1 + 1))⌋ - 1 / ((n + 1 : ℝ)) := by
          specialize hxn (n + 1) (by linarith)
          simpa using hxn
        have eq3 : x (n + 1) = (↑n + 1 : ℝ) := by
          simpa using h3
        have eq4 : x (n + 1 + 1) = (↑n + 1 + 1 : ℝ) := by
          simpa using h4
        have eq5 : Real.sqrt (x (n + 1)^2 + x (n + 1 + 1)) = Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) := by
          rw [eq3, eq4]
        have eq6 : ⌊Real.sqrt (x (n + 1)^2 + x (n + 1 + 1))⌋ = (n + 1 : ℤ) := by
          rw [eq5]
          have h7 : (↑n + 1 : ℝ)^2 < (↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ) := by
            nlinarith [show (0 : ℝ) ≤ (↑n : ℝ) by positivity]
          have h8 : (↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ) < (↑n + 2 : ℝ)^2 := by
            nlinarith [show (0 : ℝ) ≤ (↑n : ℝ) by positivity]
          have h9 : (↑n + 1 : ℝ) < Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) := by
            have h10 : (↑n + 1 : ℝ) < Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) := by
              have h11 : Real.sqrt ((↑n + 1 : ℝ)^2) < Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) := by
                apply Real.sqrt_lt_sqrt
                nlinarith
                nlinarith
              have h12 : Real.sqrt ((↑n + 1 : ℝ)^2) = (↑n + 1 : ℝ) := by
                rw [Real.sqrt_sq (show 0 ≤ (↑n + 1 : ℝ) by positivity)]
              nlinarith
            linarith
          have h10 : Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) < (↑n + 2 : ℝ) := by
            have h11 : Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)) < (↑n + 2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ) by positivity)]
            linarith
          have h13 : ⌊Real.sqrt ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ))⌋ = (n + 1 : ℤ) := by
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg ((↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ)^2 + (↑n + 1 + 1 : ℝ) by positivity)]
          exact_mod_cast h13
        rw [eq6] at eq2
        rw [eq4] at eq2
        have eq7 : x (n + 1 + 2) = (↑n + 3 : ℝ) := by
          field_simp at eq2 ⊢
          nlinarith
        simp [show n + 1 + 2 = n + 3 by omega] at eq7 ⊢
        all_goals linarith
  specialize h1 (n - 1)
  cases n with
  | zero => linarith
  | succ n => 
    simp at h1 ⊢
    all_goals
      linarith [h1]