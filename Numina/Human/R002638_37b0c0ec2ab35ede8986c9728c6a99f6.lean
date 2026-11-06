import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum

open Nat Polynomial

/-- In the expansion of $(ax + b)^{2000},$ where $a$ and $b$ are
[relatively prime](https://artofproblemsolving.com/wiki/index.php/Relatively_prime) positive
integers, the [coefficients](https://artofproblemsolving.com/wiki/index.php/Coefficient) of
$x^{2}$ and $x^{3}$ are equal. Find $a + b$. -/
theorem algebra_713 (a b : ℕ) (apos : 0 < a) (bpos : 0 < b) (h1 : a.Coprime b)
    (h2 : coeff (((C a) * X + (C b))^2000) 2 = coeff (((C a) * X + (C b))^2000) 3) :
    a + b = 667 := by

  -- Using the [binomial theorem](https://artofproblemsolving.com/wiki/index.php/Binomial_theorem),
  -- find the coefficients.
  rw [add_pow ((C a) * X) (C b) 2000, finset_sum_coeff, finset_sum_coeff] at h2
  simp only [←C_eq_natCast, coeff_mul_C, ←C_pow, coeff_mul_C, mul_pow, ←C_pow, coeff_C_mul_X_pow] at h2

  simp at h2

  -- Simplify the equation.
  replace h2 : b^1998 * (choose 2000 2) = a * b^1997 * (choose 2000 3) := by nlinarith
  replace h2 : b^1997 * (b * (choose 2000 2)) = b^1997 * (a * (choose 2000 3)) := by linarith
  replace h2 : b * (choose 2000 2) = a * (choose 2000 3) := by
    apply Nat.eq_of_mul_eq_mul_left (n := b^1997) (Nat.pow_pos bpos)
    exact h2

  have : choose 2000 2 = 1999 * 1000 := by rw [Nat.choose_eq_fast_choose]; rfl
  rw [this] at h2
  have : choose 2000 3 = 666 * 1999 * 1000 := by rw [Nat.choose_eq_fast_choose]; rfl
  rw [this] at h2

  -- Since $a$ and $b$ are relatively prime, $a = 1$ and $b = 666$.
  replace h2 : b = a * 666 := by linarith

  have ha : a = 1 := by
    apply Coprime.eq_one_of_dvd h1
    simp [h2]

  subst ha h2
  rfl