import Mathlib

/-
Let $n$ be a natural number. Let $P_4(n)$ denote the product $n(n+1)(n+2)(n+3)$.
Show that for $n \ge 1$, the inequality $(n^2+3n)^2 < P_4(n) < (n^2+3n+1)^2$ holds.
Use this to conclude that for $n \ge 1$, $P_4(n)$ cannot be the square of a natural number.
-/

theorem number_theory_639681 (n:ℕ) (hn: 1 ≤ n):
(n^2 + 3 * n)^2 < n * (n + 1) * (n + 2) * (n + 3) ∧
n * (n + 1) * (n + 2) * (n + 3) < (n^2 + 3 * n + 1)^2 ∧
¬ (IsSquare (n * (n + 1) * (n + 2) * (n + 3)))
  := by

  --The first two inequalities are easy to get using basic calculation.
  have e1 : (n ^ 2 + 3 * n) ^ 2 < n * (n + 1) * (n + 2) * (n + 3) := by
    nlinarith  
  have e2 : n * (n + 1) * (n + 2) * (n + 3) < (n^2 + 3 * n + 1)^2 := by
    nlinarith
  
  --If it is a square, then it is between n^2 + 3n and n^2 + 3n + 1, which is a contradiction.
  have cla : ¬IsSquare (n * (n + 1) * (n + 2) * (n + 3)) := by
    by_contra exi
    obtain ⟨m,hm⟩ := exi
    have : n ^ 2 + 3 * n < m := by 
      simp [hm] at e1
      nlinarith
    have : m < n ^ 2 + 3 * n + 1 := by 
      simp [hm] at e2
      nlinarith
    linarith

  tauto