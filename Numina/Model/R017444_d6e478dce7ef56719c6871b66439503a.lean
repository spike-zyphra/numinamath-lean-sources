import Mathlib

theorem algebra_11809 {a : ℕ → ℝ} (ha1 : a 1 = 2) (han : ∀ n ≥ 1, (n + 1) * a (n + 1) = a n + n) :
    ∀ n ≥ 1, a n = 1 / Nat.factorial n + 1 := by
  intro n hn
  induction n with
  | zero => 
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      rw [ha1]
      norm_num [Nat.factorial]
    | succ n => 
      have eq1 := han (n + 1) (by linarith)
      have h1 : a (n + 1) = 1 / (Nat.factorial (n + 1) : ℝ) + 1 := by
        specialize ih (by linarith)
        simpa using ih
      have eq2 : (n + 2 : ℕ) * a (n + 2) = a (n + 1) + (n + 1 : ℝ) := by
        simp [show n + 1 ≥ 1 by linarith] at eq1 ⊢
        <;> linarith
      rw [h1] at eq2 
      have eq3 : a (n + 2) = ( (1 / (Nat.factorial (n + 1) : ℝ) + 1 ) + (n + 1 : ℝ) ) / (n + 2 : ℝ) := by
        field_simp at eq2 ⊢
        nlinarith
      rw [eq3]
      field_simp [Nat.factorial]
      <;> ring_nf <;> field_simp [Nat.factorial] <;> ring