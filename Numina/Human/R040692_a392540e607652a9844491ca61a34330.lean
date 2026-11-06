import Mathlib

open Nat

/-
What is the smallest number of eggs in a basket such that when the eggs are removed 2, 3, 4, 5, or 6 at a time, there is always one egg left over, but when they are removed 7 at a time, there are no eggs left over?
-/
theorem number_theory_4712 : IsLeast {x : ℕ | x ≡ 0 [MOD 7] ∧ ∀ n ∈ ({2,3,4,5,6} : Set ℕ), x ≡ 1 [MOD n]} 301 := by
  constructor
  · dsimp [upperBounds]
    simp_all; split_ands <;> norm_cast
  · dsimp [upperBounds]
    intro a h
    simp_all
    -- First, we need to show that $\forall a, a \equiv 1 \pmod n$, where $n \in \{2,3,4,5,6\}$,
    -- we have $301 \le a$.
    -- It is easy to get that $a \equiv 1 \pmod 60$ because $a \equiv 1 \pmod 3$ and $a \equiv 1 \pmod 4$, and $a \equiv 1 \pmod 5$.
    have hlcm : a ≡ 1 [MOD 60] := by
      have h3 : a ≡ 1 [MOD 3] := by aesop
      have h4 : a ≡ 1 [MOD 4] := by aesop
      have h5 : a ≡ 1 [MOD 5] := by aesop
      have h20 : a ≡ 1 [MOD 20] := by
        rw [← (show Nat.lcm 4 5 = 20 by aesop)]
        apply Nat.mod_lcm h4 h5
      rw [← (show Nat.lcm 3 20 = 60 by aesop)]
      apply Nat.mod_lcm h3 h20
    -- Now, we can find $k$ such that $a = 60k + 1$.
    have h₁ : ∃ k, a = 60 * k + 1 := by
      dsimp [Nat.ModEq] at hlcm
      have : 60 ∣ (a - 1) := by
        rw [(show 1 = 1 % 60 by aesop)] at hlcm
        have : _ := Nat.sub_mod_eq_zero_of_mod_eq hlcm
        apply Nat.dvd_of_mod_eq_zero this
      use (a - 1) / 60
      ring_nf
      rw [Nat.div_mul_cancel this]
      by_cases h : 0 < a
      · have : 1 ≤ a := by aesop
        aesop
      · have : a = 0 := by aesop
        aesop
    obtain ⟨k,hk⟩ := h₁
    -- Substitute $a = 60k + 1$.
    subst hk
    -- On the other hand, $301 \le 60k + 1$ if and only if $5 \le k$.
    have : 301 ≤ 60 * k + 1 ↔ 5 ≤ k := by
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    -- So, the goal is to show that $5 \le k$.
    rw [this]
    -- We can do case analysis on $k$.
    -- Luckliy the goal is easy to solve under all cases.
    match k with
    | 0 => norm_cast
    | 1 => norm_cast
    | 2 => norm_cast
    | 3 => norm_cast
    | 4 => norm_cast
    | i+5 => linarith
