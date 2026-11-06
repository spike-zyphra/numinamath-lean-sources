import Mathlib
open Real
/- Let a sequence u(n) be defined by u(1) = 5 and the relationship u(n+1) - u(n) = 3 + 4(n - 1), n = 1,2,3... If u(n) is expressed as a polynomial in n, the algebraic sum of its coefficients is:
  (A)3 (B)4 (C)5 (D)6 (E)11
-/
theorem algebra_96057 {u : ℕ → ℤ} (hu1 : u 1 = 5)
(hun : ∀ n, 1≤n → u (n+1) - u n = 3+4*(n-1)):
∀ n, 1≤n → u n = 2*n*n-3*n+6 := by
  -- proving u(n)=2n^2-3n+6 by induction
  intro n hn
  induction n with
  | zero => contradiction -- n=0 case is meaningless
  | succ k hi =>
    by_cases hk:k=0
    -- n=1 case is already given by a hypothesis
    · simp [hk];norm_cast
    -- for n≥2 cases we substitute the recursive formula and inductive hypothesis into the goal
    -- and we can solve the goal by trivial simplification
    · change k≠0 at hk
      rw [← Nat.one_le_iff_ne_zero] at hk
      have hh : ((u (k + 1)):ℤ)=u k+3 + 4 * (k - 1) := by linarith [hun k hk]
      have hcast : (k:ℤ)+1=↑(k + 1) := by norm_cast
      rw [hh,hi hk,← hcast]
      linarith