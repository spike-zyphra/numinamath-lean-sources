import Mathlib

/-Let  $a$  and  $b$  be positive integers satisfying
	\[ \frac a{a-2} = \frac{b+2021}{b+2008} \]
Find the maximum value  $\dfrac ab$  can attain.-/
theorem number_theory_8530_1 (a b : ℚ) (h0 : a ≠ 2)
(ha : ∃ t : ℤ, 1 ≤ t ∧ a = t) (hb : ∃ t : ℤ, 1 ≤ t ∧ b = t)
(hab : a / (a - 2) = (b + 2021) / (b + 2008)) :
a / b ≤ 312 / 7 := by
-- It is more convenient if we introduce two more variebles of integer type when formalizing this problem
  rcases ha with ⟨a', ha'1, ha'2⟩; rcases hb with ⟨b', hb'1, hb'2⟩
-- Converting $1≤b'$ to $1≤b$
  have : 1 ≤ b := by rw [hb'2, show (1:ℚ)=(1:ℤ) by simp, Int.cast_le]; linarith
-- Rewrite the equation and solve for $b$
  rw [div_eq_div_iff, ← sub_eq_zero] at hab; ring_nf at hab
  rw [add_eq_zero_iff_neg_eq] at hab; simp at hab
-- Make a copy of the equation and rewrite an integer-type version of it
  have h'ab := hab
  rw [ha'2, hb'2, show (b':ℚ)*2=(b'*2:ℤ) by simp] at h'ab
  rw [show (a' : ℚ) * 13 - 4042 = ((a' * 13 - 4042) : ℤ) by rw [Int.cast_sub]; simp] at h'ab
  rw [Int.cast_inj] at h'ab
-- Prove that $a'$ is even and let $a'=2k$
  have d2 : 2 ∣ a' := by
    suffices d' : 2 ∣ a' * 13
    · apply Prime.dvd_or_dvd at d'
      cases d'; assumption; contradiction
      rw [Int.prime_iff_natAbs_prime]; norm_num
    rw [sub_eq_iff_eq_add] at h'ab
    rw [h'ab]; use b'+2021; ring_nf
  rcases d2 with ⟨k, hk1⟩
-- Find a lower bound for $k$
  have hk2 : 156 ≤ k := by linarith
-- Prove the final result
  rw [div_le_div_iff, Rat.le_iff_sub_nonneg, show 312*b=156*(b*2) by ring]
  symm at hab; rw [hab]; ring_nf; simp; rw [ha'2, hk1]; push_cast
  rw [mul_comm, ← mul_assoc, show (2021:ℚ)*2=4042 by norm_num]
  rw [show 4042*(k:ℚ)=((4042*k):ℤ) by simp, show (630552:ℚ)=(630552:ℤ) by simp]
  rw [Int.cast_le]; linarith
  rw [hb'2, show (0:ℚ)=(0:ℤ) by simp, Int.cast_lt]; linarith
  norm_num; by_contra h'; rw [sub_eq_zero] at h'; contradiction
  linarith
  

/-Conversely, we can check that $a$ equals $312$ and $b$ equals $7$ is a solution to the problem-/
theorem number_theory_8530_2 :
(312:ℚ) / (312 - 2) = (7 + 2021) / (7 + 2008) := by field_simp; norm_num