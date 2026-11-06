import Mathlib

/-
Problem 1. Prove that for every positive integer $n$ the following proposition holds:

"The number 7 is a divisor of $3^{n}+n^{3}$ if and only if 7 is a divisor of $3^{n} \cdot n^{3}+1$."
 -/
theorem number_theory_295886 (n : ℕ) (hn : n > 0) :
    7 ∣ 3^n + n^3 ↔ 7 ∣ 3^n * n^3 + 1 := by
  -- prove 7 is prime, will be used later
  have p7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨p7⟩
  -- case work on 7 divides n or not
  obtain h7n | h7n := @or_not (7 ∣ n)
    -- if divides, then 7 ∣ n^3,
  . have h₁ : 7 ∣ n^3 := by calc
      7 ∣ n := h7n
      _ ∣ n^3 := by exact Dvd.intro_left (n.pow 2) rfl
    have h₂ : 7 ∣ 3^n * n^3 := by exact Dvd.dvd.mul_left h₁ _
    -- this means goal is equivlaent to 7 ∣ 3^n ↔ 7 ∣ 1
    rw [← Nat.dvd_add_iff_left h₁, ← Nat.dvd_add_iff_right h₂]
    simp
    by_contra h
    -- so need to prove 7 ∣ 3 is false, which is just calculation
    have : 7 ∣ 3 := Nat.Prime.dvd_of_dvd_pow p7 h
    norm_num at this
    -- if 7 doesn't divide n, convert goal to ZMods,
  . repeat rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    -- show n^6 = 1
    have hn_pow : (n:ZMod 7)^(7-1) = 1 := by
      refine ZMod.pow_card_sub_one_eq_one ?_
      by_contra h
      have := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
      contradiction
    -- now prove two directions, in both case just mutiply by n^3, and simplify to get other target
    simp at hn_pow
    push_cast
    constructor <;> rintro h
    . have : ((3: ZMod 7)^n + (n: ZMod 7)^3) * (n: ZMod 7)^3 = 0 := by rw [h]; simp
      ring_nf at this
      rw [hn_pow] at this
      ring_nf at *
      exact this
    . have : ((3: ZMod 7)^n * (n: ZMod 7)^3 + 1) * (n: ZMod 7)^3 = 0 := by rw [h]; simp
      ring_nf at this
      rw [hn_pow] at this
      ring_nf at *
      exact this