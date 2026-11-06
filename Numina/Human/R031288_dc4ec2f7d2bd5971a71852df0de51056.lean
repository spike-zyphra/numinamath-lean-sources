import Mathlib

/- 10. Prove: When $n$ is odd, $1947 \mid\left(46^{n}+296 \cdot 13^{n}\right)$. -/
theorem number_theory_179051 (n : ℕ) (h₀ : Odd n) : 1947 ∣ (46^n + 296 * 13^n) := by
  -- We use the fact that 1947 = 3 * 11 * 59. Since all of these are coprime,
  -- it suffices to show that each of them divides the expression individually.
  rw [show 1947 = 3 * 11 * 59 by norm_num]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_) ?_
  -- Both 3 and 11 are straightforward.
  . rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul]
    rw [show (Nat.cast 46 : ZMod 3) = Nat.cast 1 by rw [ZMod.natCast_eq_natCast_iff']]
    rw [show (Nat.cast 296 : ZMod 3) = Nat.cast 2 by rw [ZMod.natCast_eq_natCast_iff']]
    rw [show (Nat.cast 13 : ZMod 3) = Nat.cast 1 by rw [ZMod.natCast_eq_natCast_iff']]
    simp
    norm_cast
  . rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul]
    rw [show (Nat.cast 46 : ZMod 11) = Nat.cast 2 by rw [ZMod.natCast_eq_natCast_iff']]
    rw [show (Nat.cast 296 : ZMod 11) = Int.cast 296 by simp]
    rw [show (Int.cast 296 : ZMod 11) = Int.cast (-1) by rw [ZMod.intCast_eq_intCast_iff']; simp]
    rw [show (Nat.cast 13 : ZMod 11) = Nat.cast 2 by rw [ZMod.natCast_eq_natCast_iff']]
    simp
  . -- For 59, we use the fact that n is odd.
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul]
    rw [show (Nat.cast 46 : ZMod 59) = Int.cast 46 by simp]
    rw [show (Int.cast 46 : ZMod 59) = Int.cast (-13) by rw [ZMod.intCast_eq_intCast_iff']; simp]
    rw [show (Nat.cast 296 : ZMod 59) = Nat.cast 1 by rw [ZMod.natCast_eq_natCast_iff']]
    simp
    rw [Odd.neg_pow h₀]
    simp