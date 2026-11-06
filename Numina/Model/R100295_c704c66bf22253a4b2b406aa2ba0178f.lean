import Mathlib

open Finset

/- Fibonacci sequence -/
def u : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => u n + u (n + 1)

lemma u_ge_1 {n} (hn : 1 ≤ n) : 1 ≤ u n :=
  match n with
  | 0 => by simp at hn
  | 1 => by decide
  | n + 2 => by
    simp only [u]
    have := u_ge_1 (show 1 ≤ n + 1 by omega)
    omega

theorem number_theory_4542 {n : ℕ} : ∑ i in Icc 1 n, u i = u (n + 2) - 1 := by 
  induction n with 
  | zero =>
    simp [u]
    <;> try { trivial }
  | succ n ih =>
    rw [sum_Icc_succ_top (by linarith)]
    simp [u] at ih ⊢
    all_goals 
      omega