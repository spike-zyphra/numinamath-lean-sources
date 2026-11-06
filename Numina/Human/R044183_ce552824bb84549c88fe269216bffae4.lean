import Mathlib

/- Let $n$ be a positive integer.  What is the greatest possible value of $\gcd(n + 7, 2n + 1)$? -/
theorem number_theory_23146 :
  IsGreatest {x | ∃ n:ℕ , n > 0 ∧ x = Nat.gcd (n + 7) (2 * n + 1)} 13 := by
  unfold IsGreatest
  constructor
  . {
    -- prove that 13 is the least upper bound
    simp
    use 6
    simp
  }
  . {
    -- prove that 13 is an upper bound
    unfold upperBounds
    simp
    intros a x _ a_def
    have a_dvd_gcd: a ∣ Nat.gcd (x + 7) (2 * x + 1) := by rw [a_def]
    have ⟨ a_dvd1, a_dvd2 ⟩ := Nat.dvd_gcd_iff.1 a_dvd_gcd
    replace a_dvd1 := Dvd.dvd.mul_left a_dvd1 2
    have a_dvd_13 := Nat.dvd_sub (by ring_nf; norm_num) a_dvd1 a_dvd2
    simp [mul_add] at a_dvd_13
    exact Nat.le_of_dvd (by norm_num) a_dvd_13
  }
