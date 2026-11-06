import Mathlib

theorem algebra_297256 {a : ℕ → ℝ} (ha1 : a 1 = -1 / 3)
    (han : ∀ n ≥ 1, a (n + 1) = (3 * a n - 1) / (3 - a n)) :
    ∀ n ≥ 1, a n = (1 - 2 ^ n) / (1 + 2 ^ n) := by
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
      simp [h3] at *
      rw [h2] at *
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
      <;> linarith