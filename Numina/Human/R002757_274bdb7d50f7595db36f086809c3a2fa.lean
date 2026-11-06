import Mathlib

open Finset
open Nat

/-
90.1. Let $m, n$, and $p$ be odd positive integers. Prove that the number


$$

\sum_{k=1}^{(n-1)^{p}} k^{m}

$$


is divisible by $n$.
 -/
theorem number_theory_109919 (m n p : ℕ) (hm : Odd m) (hn : Odd n) (hp : Odd p)
    (hpos : m > 0 ∧ n > 0 ∧ p > 0) :
    n ∣ ∑ k in Finset.Icc 1 ((n - 1)^p), k^m := by
  -- We can multiply by two since n is odd
  suffices n ∣ 2 * ∑ k in Finset.Icc 1 ((n - 1)^p), k^m by
    have coprime : Coprime n 2 := Odd.coprime_two_right hn
    exact Coprime.dvd_of_dvd_mul_left coprime this
  -- Now we use a symmetry argument
  -- Rewrite in terms of Ico
  rw [show Icc 1 ((n - 1) ^ p) = Ico 1 ((n - 1) ^ p + 1) by aesop]
  -- Reverse the order of summation to set up a symmetry argument
  have sum_reflect : ∑ k ∈ Ico 1 ((n - 1) ^ p + 1), k ^ m = ∑ k ∈ Ico 1 ((n - 1) ^ p + 1), ((n - 1) ^ p + 1 - k) ^ m := by
    have : _ := (sum_Ico_reflect (fun x => x ^ m) 1 (show (n - 1) ^ p + 1 ≤ (n - 1) ^ p + 2 by linarith)).symm
    conv at this =>
      congr
      · lhs
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
    tauto
  -- We pair terms
  suffices n ∣ ∑ k ∈ Finset.Ico 1 ((n - 1) ^ p + 1), k ^ m + ∑ k ∈ Finset.Ico 1 ((n - 1) ^ p + 1), ((n - 1) ^ p + 1 - k) ^ m by
    rw [sum_reflect, ← two_mul, ← sum_reflect] at this
    tauto
  rw [← sum_add_distrib]
  -- We will show that n divides every term of the sum
  apply dvd_sum
  intro k hk
  simp at hk
  -- First, we show that (n - 1) ^ p + 1 divides every term
  have dvd₀ : _ := Odd.nat_add_dvd_pow_add_pow k ((n - 1) ^ p + 1 - k) hm
  conv at dvd₀ =>
    lhs
    rw [Nat.add_sub_cancel' (by linarith)]
  nth_rw 2 [show 1 = 1 ^ p by simp] at dvd₀
  -- Now, we show that n divides (n - 1) ^ p + 1
  have dvd₁ : _ := Odd.nat_add_dvd_pow_add_pow (n - 1) 1 hp
  conv at dvd₁ =>
    lhs
    rw [Nat.sub_add_cancel (by linarith)]
  -- The result follows by transitivity of ∣ relation
  exact dvd_trans dvd₁ dvd₀