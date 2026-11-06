import Mathlib

theorem number_theory_116534 {a b : ℕ} (hb : b ≠ 0) (h : a / b = 14 ∧ a % b = 18) (h' : a - 3 * b = 135) :
    IsSquare (2 * a) := by
  rcases h with ⟨ha1, ha2⟩
  have h1 : a = 14 * b + 18 := by
    rw [←Nat.div_add_mod a b, ha1, ha2]
    all_goals linarith
  rw [h1] at h'
  -- Let's compute $a - 3b = 135$ becomes $(14b + 18) - 3b = 135$
  -- so $11b + 18 = 135$, $11b = 117$ which is impossible because $117$
  -- is not divisible by $11$. Therefore Lean will derive a contradiction:
  omega -- omega will detect this contradiction automatically