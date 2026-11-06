import Mathlib

theorem algebra_326141 {x : ℕ → ℝ} (hx1 : x 1 = 3)
    (hxn : ∀ n ≥ 1, x (n + 1) = (2 / (n ^ 2) + 3 / n + 1) * x n + n + 1) :
    ∀ n ≥ 1, x n = n ^ 2 * (2 * n + 1) := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      rw [hx1]
      norm_num
    | succ n =>
      have ih' := ih (Nat.succ_le_of_lt (Nat.succ_pos _))
      rw [hxn (n + 1) (by linarith)]
      simp [ih']
      field_simp
      ring