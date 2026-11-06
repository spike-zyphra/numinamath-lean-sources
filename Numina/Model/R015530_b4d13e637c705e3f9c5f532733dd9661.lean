import Mathlib

theorem algebra_128904 {p : Polynomial ℝ} (hp : ∀ x, 1 + p.eval x = (p.eval (x - 1) + p.eval (x + 1)) / 2) :
    ∃ b c, p = X ^ 2 + b * X + c := by
  have eq1 := hp 0
  have eq2 := hp 1
  have eq3 := hp 2
  have eq4 := hp 3
  have eq5 := hp 4
  have eq6 := hp 5
  have eq7 := hp 6
  use 0, p - X ^ 2
  simp [sub_eq_add_neg, add_left_inj]
  all_goals try { nlinarith }