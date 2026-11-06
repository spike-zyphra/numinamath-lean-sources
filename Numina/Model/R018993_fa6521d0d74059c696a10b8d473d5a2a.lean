import Mathlib

theorem algebra_328406 {a : ℕ → ℝ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + (-1) ^ n * n + 1) :
    ∀ n ≥ 1, a n = (8 / 9) * 2 ^ n + (1 / 9 - n / 3) * (-1) ^ n - 1 := by 
  intro n hn
  induction n with
  | zero => 
    exfalso 
    linarith 
  | succ n ih => 
    cases n with
    | zero => 
      rw [ha1]
      norm_num 
    | succ n => 
      have h2 := ih (by linarith)
      have h3 := han (n + 1) (by linarith)
      simp [h2] at h3 ⊢ 
      ring_nf at h3 ⊢ 
      <;> field_simp at h3 ⊢ 
      <;> ring_nf at h3 ⊢ 
      <;> linarith