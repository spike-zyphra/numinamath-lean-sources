import Mathlib

open Nat

/- Let $L$ be a positive integer such that $L \equiv 4 \pmod 9$.
Let $A, B$ be natural numbers representing digits (i.e. $0 \le A \le 9$ and $0 \le B \le 9$).
Let $N$ be the $(3+2L)$-digit number whose decimal representation consists of the digit $3$, followed by digit $A$, followed by digit $B$, followed by $L$ repetitions of the pair of digits $7, 6$. (For example, if $L=1$, $N$ is the number $3AB76$; if $L=2$, $N$ is $3AB7676$).
Suppose $N$ is divisible by $9$. Suppose further that $A < B < 6$.
Show that $B-A=2$. -/
theorem number_theory_638307
  {L : ℕ}
  (hL : L > 0)
  (hL1 : L ≡ 4 [MOD 9])
  {A B : ℕ}
  (hA : A < B)
  (hB : B < 6)
  (N : ℕ)
  (hN : (Nat.digits 10 N).sum = 3 + A + B + 7 * L + 6 * L)
  : 9 ∣ N → B - A = 2 :=
by
  intro H
  have : 0 ≡ (Nat.digits 10 N).sum [MOD 9] := by
    trans N
    . simp [Nat.ModEq]
      symm
      exact dvd_iff_mod_eq_zero.mp H
    . exact modEq_nine_digits_sum N
  rw [hN] at this
  ring_nf at this
  have : L * 13 ≡ 7 [MOD 9] := by
    exact ModEq.mul hL1 rfl
  have : 0 ≡ 3 + A + B + 7 [MOD 9] := by
    trans 3 + A + B + L * 13
    . assumption
    . apply Nat.ModEq.add_left
      assumption
  ring_nf at this
  have : 0 ≡ 1 + A + B [MOD 9] := by
    rw [add_assoc] at this ⊢
    trans 10 + (A + B)
    . assumption
    . apply Nat.ModEq.add_right
      decide
  -- Now simply try each cases.
  interval_cases B
  all_goals interval_cases A
  all_goals try simp [Nat.ModEq] at this
  rfl
