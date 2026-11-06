import Mathlib

/-When the least common multiple of two positive integers is divided by their greatest common divisor, the result is 33. If one integer is 45, what is the smallest possible value of the other integer?-/
theorem number_theory_15085 : IsLeast {n : ℕ | Nat.lcm 45 n / Nat.gcd 45 n = 33} 165 := by
-- Introduce variables and assumptions
  rw [IsLeast, lowerBounds]; simp; constructor; norm_num
  intro m hm
-- Prove that $m$ is positive
  have mpos : 0 < m := by by_contra; simp_all
-- Apply the lemma Nat.gcd_mul_lcm to get a multiplication relation
-- then rewrite assumptions
  have lcm1 := Nat.gcd_mul_lcm 45 m; symm at lcm1
  rw [← Nat.div_eq_iff_eq_mul_right] at lcm1; symm at lcm1
  rw [lcm1, Nat.div_div_eq_div_mul, ← pow_two] at hm
  rw [Nat.div_eq_iff_eq_mul_left] at hm
  nth_rw 1 [show 45=3*15 by norm_num, mul_assoc] at hm
  rw [show 33=3*11 by norm_num, mul_assoc] at hm; simp at hm
-- Prove that $165$ divides $m$ by rewriting $165$ as $Nat.lcm 11 15$,
-- then prove $11$ divides $m$ and $15$ divides $m$
  have : 165 ∣ m := by
    rw [show 165 = Nat.lcm 11 15 by norm_num]; apply Nat.lcm_dvd
    · have : 11 ∣ 15 * m := by use Nat.gcd 45 m ^ 2
      rw [Nat.Prime.dvd_mul] at this; cases this
      contradiction; assumption; norm_num
    have : 15 ∣ Nat.gcd 45 m := by
      rw [show 15=Nat.lcm 3 5 by norm_num]; apply Nat.lcm_dvd
      · rw [← Prime.dvd_pow_iff_dvd _ (show 2≠0 by norm_num)]
        have : 3 ∣ 11 * Nat.gcd 45 m ^ 2 := by rw [← hm]; use 5*m; ring
        rw [Nat.Prime.dvd_mul] at this; cases this; contradiction
        assumption; norm_num
        rw [← Nat.prime_iff]; norm_num
      rw [← Prime.dvd_pow_iff_dvd _ (show 2≠0 by norm_num)]
      have : 5 ∣ 11 * Nat.gcd 45 m ^ 2 := by rw [← hm]; use 3*m; ring
      rw [Nat.Prime.dvd_mul] at this; cases this; contradiction
      assumption; norm_num
      rw [← Nat.prime_iff]; norm_num
    rcases this with ⟨k, hk⟩; rw [hk] at hm; ring_nf at hm
    rw [show 2475=11*15*15 by norm_num, ← mul_assoc, ← mul_assoc] at hm
    simp at hm; use k^2*11; rw [hm]; ring
-- Apply Nat.le_of_dvd and finish the final goals
  apply Nat.le_of_dvd; any_goals assumption
  rw [pow_pos_iff]; apply Nat.gcd_pos_of_pos_right; assumption
  norm_num; rw [pow_two]; apply mul_dvd_mul
  apply Nat.gcd_dvd_left; apply Nat.gcd_dvd_right
  apply Nat.gcd_pos_of_pos_right; assumption
  rw [dvd_mul]; use Nat.gcd 45 m; use 1
  simp; apply Nat.gcd_dvd_left