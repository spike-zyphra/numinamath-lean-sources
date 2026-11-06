import Mathlib

open Nat
/-
Theorem: January 1, of the year ($2000-K$) (astronomical year numbering, proleptic Gregorian calendar) was on the day of the week $D$, where $D \equiv (6 - (K + L_K)) \pmod 7$. (Here Sunday is 0, Monday is 1, ..., Saturday is 6).
-/
theorem NYD_date_correct (K : ℕ) :
  let leap (y : ℕ) : Bool :=
    (y % 4 = 0 ∧ y % 100 ≠ 0) ∨ (y % 400 = 0)
  let years := (List.range K).map (fun k => 2000 - K + k)
  let L := (years.filter leap).length
  let D := (6 - (K + L) % 7) % 7
  (D + 365 * K + L) % 7 = 6 % 7 := by

  -- Introduction of local variables for the proof
  intro leap
  intro Y
  intro L
  intro D

  -- Prove that 365 days is congruent to 1 modulo 7 (i.e., 365 ≡ 1 mod 7)
  have h365 : 365 % 7 = 1 := by norm_num

  -- Apply modular arithmetic properties to simplify the expression
  rw[add_mod,add_mod D,mul_mod,h365,one_mul,←add_mod,mod_mod K]
  dsimp only[D]
  ring_nf
  rw[mod_mod,add_mod,←add_mod,add_assoc,add_mod,←add_mod (6 - (K + L) % 7),←add_mod]
  ring_nf

  -- Define S as the sum of leap years (L) and total years (K)
  let S := L + K

  -- Prove that any natural number S can be written in the form 7k + r (remainder when divided by 7)
  have hS : ∃ k, S = 7 * k + S%7 := by
    use S / 7
    symm
    exact Nat.div_add_mod S 7

  -- Destructure the existential proof to get the quotient k and remainder
  obtain ⟨k, hk⟩ := hS

  -- Prove that the expression (S + (6 - S % 7)) modulo 7 equals 6
  have h : (S + (6 - S % 7)) % 7 = 6 := by
    rw[hk,add_assoc,add_mod,mul_mod_right,zero_add,add_mod (7*k),mul_mod_right,zero_add]
    rw[mod_mod,mod_mod,mod_mod]
    let r := S % 7
    have hr : r < 7 := Nat.mod_lt S (by decide)
    have h_sub : 6 - r ≤ 6 := Nat.sub_le 6 r
    calc
      (r + (6 - r)) % 7 = 6 % 7 := by rw [Nat.add_sub_of_le (by linarith)]
      _ = 6 := by rw [Nat.mod_eq_of_lt (by decide)]

  -- Replace the simplified expression with the proven result
  rw[h]
