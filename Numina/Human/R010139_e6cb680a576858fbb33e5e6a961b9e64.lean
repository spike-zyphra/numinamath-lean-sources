import Mathlib

/-Given that $a$ is a multiple of $456$, find the greatest common divisor of $3a^3+a^2+4a+57$ and $a$.-/
theorem number_theory_11854 (a : ℕ) (ha : 456 ∣ a) :
    gcd (3 * a ^ 3 + a ^ 2 + 4 * a + 57) a = 57 := by
  -- We use the Euclidean Algorithm.  \begin{align*}
  -- \text{gcd}\,(3a^3+a^2+4a+57,a)
  -- &=\text{gcd}\,(3a^3+a^2+4a+57-(3a^2+a+4)a,a)\\
  -- &=\text{gcd}\,(57,a).
  -- \end{align*}Since $57$ is a divisor of $456$, and $a$ is a multiple of $456$, the greatest common divisor is $\boxed{57}$.
  have : gcd (3 * a ^ 3 + a ^ 2 + 4 * a + 57) a
       = gcd 57 a := by
    rw [gcd_eq_nat_gcd, gcd_eq_nat_gcd]
    refine Eq.symm (Nat.ModEq.gcd_eq ?h)
    refine Nat.modEq_of_dvd ?h.a
    simp
    norm_cast
    use (3 * a^2 + a + 4)
    linarith
  rw [this, propext (gcd_eq_left_iff 57 a rfl)]
  have : 456 = 57 * 8 := by norm_num
  rw [this] at ha
  exact dvd_of_mul_right_dvd ha
