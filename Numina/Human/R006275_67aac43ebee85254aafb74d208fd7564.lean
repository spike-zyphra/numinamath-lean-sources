import Mathlib

/- Define f(k) to be the square of the sum of the digits of k. -/
def f k := (Nat.digits 10 k).sum ^ 2

/- Let $f_1(k)$ denote the square of the sum of the digits of a positive integer $k$. For $n \ge 2$, define $f_n(k) = f_1(f_{n-1}(k))$. Let $M$ be an integer such that $M \ge 4$. Show that $f_M(11) = 169$ if $M$ is even, and $f_M(11) = 256$ if $M$ is odd. -/
theorem number_theory_635441 (M : ℕ) (hM : 4 ≤ M) :
    f^[M] 11 = if Even M then 169 else 256 := by
  -- We induct on M.
  induction M, hM using Nat.le_induction with
  | base =>
    -- We calculate f^[4] 11 to check the base case.
    simp [f, show Even 4 from ⟨2, rfl⟩]
  | succ M hM ih =>
    -- For the inductive step, we use the fact that f^[M + 1] = f (f^[M] 11).
    simp only [Function.iterate_succ', Function.comp_apply, f]
    -- We split into the cases where M is even and odd.
    rcases Nat.even_or_odd M with hMe | hMo
    . -- If M is even, then M + 1 is odd(not even).
      simp [ih, hMe, show ¬Even (M + 1) from Nat.not_even_iff_odd.mpr (Even.add_one hMe)]
    . -- If M is odd(not even), then M + 1 is even.
      simp [ih, show ¬Even M from Nat.not_even_iff_odd.mpr hMo, show Even (M + 1) from Odd.add_one hMo]