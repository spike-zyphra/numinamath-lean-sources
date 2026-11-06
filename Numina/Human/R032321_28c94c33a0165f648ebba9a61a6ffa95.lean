import Mathlib

open Polynomial

/- 32.32. Prove that the Chebyshev polynomials $T_{n}(x)$ and $T_{m}(x)$ have the following property: $T_{n}\left(T_{m}(x)\right)=T_{m}\left(T_{n}(x)\right)$. -/
theorem algebra_231255 {n m : ℤ} {T : ℤ → ℝ[X]} (hT : T = Chebyshev.T ℝ) :
    ∀ x, (T n).eval ((T m).eval x) = (T m).eval ((T n).eval x) := by
  intro x
  -- It is enough to show that T_n(T_m) = T_m(T_n).
  suffices (T n).comp (T m) = (T m).comp (T n) by
    apply_fun Polynomial.eval x at this
    simp at this
    exact this
  -- We have the following identity for Chebyshev polynomials:
  -- T_m(T_n) = T_(m * n).
  -- The result follows from T_(m * n) = T_(n * m).
  simp_rw [hT, ← Chebyshev.T_mul, mul_comm]