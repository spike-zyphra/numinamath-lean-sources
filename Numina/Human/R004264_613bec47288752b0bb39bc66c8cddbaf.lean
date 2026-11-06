import Mathlib

open Finset
open Nat

/- 1. Let $p$ be a prime number greater than 2. For $k=1,2, \ldots, p-1$, let $a_{k}$ denote the remainder of the division of the number $k^{p}$ by $p^{2}$. Prove that


$$

a_{1}+a_{2}+\ldots+a_{p-1}=\frac{p^{3}-p^{2}}{2}

$$
 -/
theorem number_theory_246671 (p : ℕ) (hp : Nat.Prime p) (hp1 : p > 2)
    (a : ℕ → ℕ) (ha : ∀ k ∈ Finset.Icc 1 (p - 1), a k = k ^ p % p ^ 2) :
    ∑ i ∈ Finset.Icc 1 (p - 1), a i = (p ^ 3 - p ^ 2) / 2 := by
  -- Rewrite in terms of Ico
  rw [show Icc 1 (p - 1) = Ico 1 p by aesop]
  -- Reverse the order of summation to set up a symmetry argument
  have sum_reflect : ∑ i ∈ Ico 1 p, a (p - i) = ∑ i ∈ Ico 1 p, a i := by
    nth_rw 2 [show Ico 1 p = Ico (p + 1 - p) (p + 1 - 1) by aesop]
    exact sum_Ico_reflect a 1 (by linarith)
  -- We pair terms
  suffices ∑ i ∈ Finset.Ico 1 p, a i + ∑ i ∈ Finset.Ico 1 p, a (p - i) = p ^ 3 - p ^ 2 by
    rw [sum_reflect, ← two_mul] at this
    omega
  rw [← sum_add_distrib]
  -- It's sufficient to show that each pair sums to p ^ 2
  suffices ∀ i ∈ Ico 1 p, a i + a (p - i) = p ^ 2 by
    -- A simple calculation
    rw [sum_congr (by rfl) this]
    simp
    rw [Nat.sub_one_mul]
    nth_rw 1 [show p = p ^ 1 by simp]
    rw [← pow_add]
  -- Show that each pair sums to p ^ 2
  intro i hi
  -- Show that p - i still lies in the bounds
  have : p - i ∈ Icc 1 (p - 1) := by
    simp
    simp at hi
    constructor
    · -- 1 ≤ p - i
      apply Nat.le_sub_of_add_le'
      linarith
    -- p ≤ p - 1 + i
    rw [← Nat.sub_add_comm (by linarith), Nat.add_sub_assoc (by tauto)]
    exact le_self_add
  rw [ha i hi, ha (p - i) this]
  -- Show that each term is less than p ^ 2
  have lt_p_sq : i ^ p % p ^ 2 < p ^ 2 ∧ (p - i) ^ p % p ^ 2 < p ^ 2 := ⟨Nat.mod_lt (i ^ p) (by positivity), Nat.mod_lt ((p - i) ^ p) (by positivity)⟩
  -- Introduce a variable shorthand
  let s := i ^ p % p ^ 2 + (p - i) ^ p % p ^ 2
  have : s < 2 * p ^ 2 := by rw [two_mul]; linear_combination Nat.add_lt_add lt_p_sq.left lt_p_sq.right
  -- Show that p ^ 2 divides the sum of each pair
  have add_reflect : p ^ 2 ∣ s := by
    unfold s
    -- Remove unnecessary mods
    rw [dvd_iff_mod_eq_zero, ← add_mod, ← dvd_iff_mod_eq_zero]
    zify
    -- Expand (p - i) ^ p
    rw [cast_sub (by simp at hi; linarith), sub_pow]
    -- Split off the first two terms
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by linarith), sum_eq_sum_Ico_succ_bot (by linarith)]
    simp
    -- Rewrite the powers of -1
    have : Odd p := Prime.odd_of_ne_two hp (by linarith)
    have : Even (1 + p) := Odd.one_add this
    rw [Odd.neg_one_pow (by tauto), Even.neg_one_pow (by tauto)]
    simp
    -- Begin elimination of the i ^ (p - 1) term
    rw [mul_assoc, mul_comm, mul_assoc, ← pow_two, mul_comm]
    apply dvd_add
    · -- Eliminate i ^ (p - 1) term
      simp
    -- Shift indices by 2
    nth_rw 2 [show 2 = 0 + 2 by simp]
    rw [show p + 1 = (p - 1) + 2 by simp; exact (Nat.sub_add_cancel (show 1 ≤ p by linarith)).symm]
    rw [← sum_Ico_add]
    -- Factor out a p ^ 2
    conv =>
      rhs
      congr
      · skip
      intro x
      -- Use a sequence of rewrites to balloon p ^ 2 to the outside
      rw [pow_add (p : ℤ) 2 x, mul_comm ((p : ℤ) ^ 2), ← mul_assoc, mul_assoc _ ((p : ℤ) ^ 2), mul_comm ((p : ℤ) ^ 2), ← mul_assoc, mul_assoc, mul_comm, mul_assoc]
    rw [← mul_sum]
    simp
  -- Show that s is positive
  have s_pos : 0 < s := by
    -- It's enough to show that one summand is positive
    suffices i ^ p % p ^ 2 ≠ 0 by
      unfold s
      rw [← pos_iff_ne_zero] at this
      calc
        0 < i ^ p % p ^ 2 := this
        _ ≤ _ := le_self_add
    -- Show that i ^ p is not divisible by p ^ 2
    intro h
    rw [← dvd_iff_mod_eq_zero] at h
    apply dvd_of_pow_dvd (by norm_num) at h
    apply Nat.Prime.dvd_of_dvd_pow (hp) at h
    -- p doesn't divide i because it's too small
    have : 0 < i ∧ i < p := by simp at hi; tauto
    exact not_dvd_of_pos_of_lt this.1 this.2 h
  -- Introduce the quotient of s and p ^ 2
  rcases add_reflect with ⟨k, hk⟩
  -- This quotient is 1 by bounding
  have k_eq_one : k = 1 := by
    -- Have k < 2
    have : k < 2 := by
      rw [hk, mul_comm, Nat.mul_lt_mul_right (by positivity)] at this
      tauto
    -- Have k positive
    have : 0 < k := by
      rw [hk] at s_pos
      exact Nat.pos_of_mul_pos_left s_pos
    -- So k must be 1
    linarith
  -- Plug the value of k in
  rw [k_eq_one, mul_one] at hk
  tauto