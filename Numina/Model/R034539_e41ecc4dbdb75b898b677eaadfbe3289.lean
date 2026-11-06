import Mathlib

theorem algebra_9079
    (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 1 / 4)
    (h₂ : ∀ n ≥ 2, a (n + 1) = ((n - 1) * a n) / (n - a n)) :
    ∀ n ≥ 1, a n = 1 / (3 * n - 2) := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    exfalso
    linarith
  | succ n =>
    cases n with
    | zero =>
      rw [h₀]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [h₁]
        norm_num 
      | succ n =>
        -- Need to find a formula for n+3 using theIH abd recurrence relation
        have h3 := ih (n + 1) (by linarith)
        have h4 := ih (n + 2) (by linarith)
        have eq1 := h₂ (n + 2) (by linarith)
        simp [show n + 2 + 1 = n + 3 by omega] at eq1 ⊢ 
        rw [eq1]
        simp [h4]
        field_simp [(show (3 * ((↑n : ℝ) + 2) - 2) ≠ 0 by nlinarith),
            (show (↑n + 2 : ℝ) - (1 / (3 * ((↑n : ℝ) + 2) - 2) : ℝ) ≠ 0 by
              rw [show (3 * ((↑n : ℝ) + 2) - 2) = (3 * (↑n + 2) - 2) by ring]
              field_simp [(show (3 * ((↑n : ℝ) + 2) - 2) ≠ 0 by nlinarith)]
              <;> nlinarith
            )
          ]
        <;> ring_nf <;> field_simp
        <;> ring