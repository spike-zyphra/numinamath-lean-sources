import Mathlib

/- Example 1 (1st International Mathematical Olympiad) (1) Given integers $a, b, c, d$ satisfying $a d-b c=1$. Find: $\frac{a+b}{c+d}$ is a reduced fraction (i.e., $a+b$ and $c+d$ are coprime).
(2) Prove that for any natural number $n$, the fraction $\frac{21 n+4}{14 n+3}$ is irreducible (i.e., it is a reduced fraction). -/

theorem number_theory_195226 {a b c d : ℤ} (h : a * d - b * c = 1) :
    IsCoprime (a + b) (c + d) := by
  -- - c * (a + b) + a * (c + d) = a * d - b * c = 1
  use -c, a
  linarith

theorem number_theory_195227 (n : ℕ) :
    Nat.Coprime (21 * n + 4) (14 * n + 3) := by
  -- We apply the Euclidean algorithm
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← Nat.gcd_sub_self_left (by linarith)]
  rw [(by omega : 21 * n + 4 - (14 * n + 3) = 7 * n + 1)]
  rw [← Nat.gcd_sub_self_right (by linarith)]
  rw [(by omega : 14 * n + 3 - (7 * n + 1) = 7 * n + 2)]
  rw [← Nat.gcd_sub_self_right (by linarith)]
  rw [(by omega : 7 * n + 2 - (7 * n + 1) = 1)]
  exact Nat.gcd_one_right (7 * n + 1)