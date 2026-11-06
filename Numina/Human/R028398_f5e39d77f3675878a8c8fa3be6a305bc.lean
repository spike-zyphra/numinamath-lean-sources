import Mathlib

/- $6 \cdot 2$ A function $f$ defined on the positive integers satisfies:
$$
f(n)=\left\{\begin{array}{l}
n-3 \\
f(f(n+7))
\end{array}\right.
$$
(when $n \geqslant 1000$),
(when $n<1000$).
Find $f(90)$. -/
theorem number_theory_109171 (f : ℕ → ℕ)
    (h₀ : ∀ n, f n = if n ≥ 1000 then n - 3 else f (f (n + 7))) :
    f 90 = 999 := by
  -- Show that f 90 = f^[n + 1] (90 + 7 * n) for all n such that 90 + 7 * n ≤ 1000.
  have h1 n (hn : 90 + 7 * n ≤ 1000) : f (90) = f^[n + 1] (90 + 7 * n)  := by
    -- Proof by induction.
    induction n with
    -- If n = 0 then f 90 = f^[1] 90.
    | zero => simp
    | succ n ih =>
      -- Consider n + 1 such that 90 + 7 * (n + 1) ≤ 1000.
      -- We have f 90 = f^[n + 1] (90 + 7 * n) (by the induction hypothesis)
      --              = f^[n] (f (90 + 7 * n)) = f^n (f(f(90 + 7 * n + 7))) (since 90 + 7 * n < 1000)
      --              = f^[n + 2] (90 + 7 * (n + 1)).
      rw [ih (by omega), Function.iterate_succ, Function.comp]
      simp [h₀ (90 + 7 * n), show ¬ 90 + 7 * n ≥ 1000 by omega]
      ring_nf
  -- We get f 90 = f^[131] 1000.
  rw [h1 130 (by norm_num)]
  -- Compute f^[1] 1000 = 997.
  have hf1 : f^[1] 1000 = 997 := by simp [h₀]
  -- Compute f^[2] 1000 = 998.
  have hf2 : f^[2] 1000 = 998 := by simp [h₀]
  -- Compute f^[3] 1000 = 999.
  have hf3 : f^[3] 1000 = 999 := by simp [h₀]
  -- Compute f^[4] 1000 = 1000.
  have hf4 : f^[4] 1000 = 1000 := by simp [h₀]
  -- Show that f^[4 * n] 1000 = 1000 for all n.
  have h2 n : f^[4 * n] 1000 = 1000 := by
    -- Proof by induction.
    induction n with
    -- f^[4 * 0] 1000 = 1000.
    | zero => simp
    | succ n ih =>
      -- f^[4 * (n + 1)] 1000 = f^[4 * n + 4] 1000 = f^[4 * n] (f^[4] 1000)
      --          = f^[4 * n] 1000 = 1000 (by the induction hypothesis).
      rw [mul_add, Function.iterate_add_apply, mul_one, hf4, ih]
  -- We have 131 = 3 + 4 * 32 so
  -- f^[131] 1000 = f^[3 + 4 * 32] 1000 = f^[3] (f^[4 * 32] 1000) = f^[3] 1000 = 999.
  rw [show 130 + 1 = 3 + 4 * 32 by norm_num]
  rw [Function.iterate_add_apply, h2, hf3]