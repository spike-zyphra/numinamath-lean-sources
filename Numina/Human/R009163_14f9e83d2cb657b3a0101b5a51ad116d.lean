
import Mathlib

/-What numeral is in the 100th decimal place in the decimal representation of $\frac{6}{7}$?-/

theorem algebra_14247 (x : ℕ) (hx : x = 10  ^ 100 * 6 / 7): (Nat.digits 10 (x)).length = 100 ∧ (Nat.digits 10 (x))[0]! = 1 := by
    --The decimal representation of $\frac{6}{7}$ is $0.\overline{857142}$, which repeats every 6 digits. Since 100 divided by 6 has a remainder of 4, the 100th digit is the same as the fourth digit following the decimal point, which is $\boxed{1}$.
    ring_nf at hx;
    rw[hx]
    norm_num
