import Mathlib

theorem algebra_237684 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n) :
    ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih => 
    cases n with
    | zero => 
      simp at *
      <;> norm_num [ha1] at *
      <;> linarith
    | succ n => 
      have h1 := ih (by linarith)
      have eq1 := han (n + 1) (by linarith)
      have eq2 := han (n + 2) (by linarith)
      simp [Finset.sum_Icc_succ_top, mul_add, add_mul] at eq1 eq2 ⊢
      simp [h1] at eq1 eq2 ⊢
      field_simp at eq1 eq2 ⊢
      ring_nf at eq1 eq2 ⊢
      nlinarith