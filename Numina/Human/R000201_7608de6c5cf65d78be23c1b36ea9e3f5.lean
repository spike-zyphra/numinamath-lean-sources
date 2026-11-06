import Mathlib

open Nat BigOperators

/-a) Exist  $a, b, c, \in N$ , such that the numbers  $ab+1,bc+1$   and  $ca+1$  are simultaneously even perfect squares ?
 b) Show that there is an infinity of natural numbers (distinct two by two)  $a, b, c$  and  $d$ , so that the numbers  $ab+1,bc+1, cd+1$  and  $da+1$  are simultaneously perfect squares.-/
theorem number_theory_8545 (a b c : ℕ):
¬ (∃ x y z, a * b + 1 = 4 * x ^ 2 ∧ b * c + 1 =4 * y ^ 2 ∧ c * a + 1 = 4 * z ^ 2) ∧ 
Set.Infinite {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
c ≠ d ∧ IsSquare (a * b + 1) ∧ IsSquare (b * c + 1) ∧ IsSquare (c * d + 1) ∧
IsSquare (d * a + 1)} := by
-- Prove that $ab+1,bc+1$ and $ca+1$ can't be simultaneously even perfect squares
  constructor
  · rintro ⟨x, y, z, h1, h2, h3⟩
    have t0 : 1 ≤ x ^ 2 ∧ 1 ≤ y ^ 2 ∧ 1 ≤ z ^ 2 := by
      constructor
      · rw [Nat.one_le_iff_ne_zero]; intro hx; simp at hx
        rw [hx] at h1; simp at h1
      constructor
      · rw [Nat.one_le_iff_ne_zero]; intro hy; simp at hy
        rw [hy] at h2; simp at h2
      rw [Nat.one_le_iff_ne_zero]; intro hz; simp at hz
      rw [hz] at h3; simp at h3
-- Prove that $ab,bc$ and $ca$ modulo $4$ is $3$
    have t1 : a * b ≡ 3 [MOD 4] := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']; use x^2-1; symm
      rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, show 4*1=1+3 by simp, ← Nat.sub_add_comm]
      rw [← add_assoc, Nat.add_sub_cancel]; symm; assumption; linarith; linarith; linarith
    have t2 : b * c ≡ 3 [MOD 4] := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']; use y^2-1; symm
      rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, show 4*1=1+3 by simp, ← Nat.sub_add_comm]
      rw [← add_assoc, Nat.add_sub_cancel]; symm; assumption; linarith; linarith; linarith
    have t3 : c * a ≡ 3 [MOD 4] := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']; use z^2-1; symm
      rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, show 4*1=1+3 by simp, ← Nat.sub_add_comm]
      rw [← add_assoc, Nat.add_sub_cancel]; symm; assumption; linarith; linarith; linarith
-- Prove that the square of $abc$ modulo $4$ is $3$, which is impossible since $3$ is not a square modulo $4$
    have t4 := Nat.ModEq.mul (Nat.ModEq.mul t1 t2) t3
    ring_nf at t4; rw [show a^2*b^2*c^2=(a*b*c)^2 by ring] at t4
    replace t4 := Nat.ModEq.trans t4 (show 27≡3[MOD 4] by rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']; norm_num; norm_num)
-- Prove that $3$ is not a square modulo $4$ by a case to case study on the remainders $m%4$
    have t5 : ∀ m, ¬ m ^ 2 ≡ 3 [MOD 4] := by
      intro m hm0
      have hm1 : m ≡ m % 4 [MOD 4] := by
        rw [Nat.ModEq.comm]; apply Nat.mod_modEq
      have := Nat.ModEq.mul hm1 hm1
      rw [← pow_two, Nat.ModEq.comm] at this
      replace this := Nat.ModEq.trans this hm0
      have hm2 : m % 4 < 4 := by apply Nat.mod_lt; norm_num
      rw [Nat.lt_iff_add_one_le] at hm2; simp at hm2; rw [Nat.le_iff_lt_or_eq] at hm2
      rcases hm2 with h | h
      · rw [Nat.lt_iff_add_one_le] at h; simp at h; rw [Nat.le_iff_lt_or_eq] at h
        rcases h with h | h
        · rw [Nat.lt_iff_add_one_le] at h; simp at h; rw [Nat.le_iff_lt_or_eq] at h
          rcases h with h | h
          · simp at h; rw [h] at this; simp at this
            rw [Nat.ModEq.comm, Nat.modEq_zero_iff_dvd] at this; contradiction
          rw [h] at this; simp at this; rw [Nat.ModEq.comm, Nat.modEq_iff_dvd] at this; contradiction
        rw [h] at this; simp at this; rw [Nat.ModEq.comm, Nat.modEq_iff_dvd] at this; contradiction
      rw [h] at this; simp at this; rw [Nat.ModEq.comm, Nat.modEq_iff_dvd] at this; contradiction
    have := t5 (a * b * c)
    contradiction
  
-- Prove that the set in question is infinite by constructing an injective map from $ℕ$ to it
  let F (n : ℕ) : ℕ × ℕ × ℕ × ℕ := (n+1, n+3, n+5, 0)
  have hF2 : Set.InjOn F Set.univ := by
    rw [← Set.injective_iff_injOn_univ]
    intro x1 x2 h12; simp [F] at h12; assumption
  apply Set.infinite_of_injOn_mapsTo hF2
  simp; intro n; constructor
  · use n+2; ring
  use n+4; ring
  rw [Set.infinite_univ_iff]; apply @Denumerable.instInfinite ℕ