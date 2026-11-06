import Mathlib

theorem number_theory_246967 (x y : ℕ → ℤ)
    (hx1 : x 1 = 2) (hy1 : y 1 = 3)
    (hxn : ∀ k ≥ 1, x (k + 1) = 3 * x k + 2 * y k ∧ y (k + 1) = 4 * x k + 3 * y k) :
    ∀ n ≥ 1, 2 * (x n)^2 + 1 = (y n)^2 := by 
  intro n hn
  induction n with 
  | zero => 
    exfalso
    omega 
  | succ n ih =>
    cases n with
    | zero => 
      have hx1' : x 1 = 2 := hx1
      have hy1' : y 1 = 3 := hy1
      simp [hx1', hy1']
      all_goals norm_num
    | succ n => 
      have h1 := ih (by linarith)
      have h2 := hxn (n+1) (by linarith)
      rcases h2 with ⟨hx2, hy2⟩
      simp [hx2, hy2] at *
      nlinarith [h1]