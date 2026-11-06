import Mathlib

/-
Let $b$ be an integer greater than $1$. Let $S_2(b) = (b-1)^{b-1} + (b^2-1)^{b^2-1}$.
Show that $b^2$ divides $S_2(b)$ and $b^3$ does not divide $S_2(b)$ if and only if $b=2$.
-/


--Two lemmas about the residue of b-1 and b^2-1 mod b.
lemma l1 (b:ℕ):
  ((b:ℤ) - 1) ≡ -1 [ZMOD (b:ℤ)] := by
  refine Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) ?_)
  simp

lemma l2 (b:ℕ):
  ((b:ℤ)^2 - 1) ≡ -1 [ZMOD (b:ℤ)] := by
  refine Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) ?_)
  simp
  use b
  ring



theorem number_theory_638520 (b s2b: ℕ) (bg1 : 1 < b) (hs: s2b = (b-1)^(b-1) + (b^2-1)^(b^2-1)):
  b^2 ∣ s2b ∧ (¬b^3 ∣ s2b) ↔ b=2 := by

  simp_all
  clear hs


  --From left to right. We will prove a stronger them that if b divides s2b, then b=2.
  constructor
  intro h
  obtain ⟨h1,h2⟩ := h
  obtain ⟨k,hk⟩ := h1
  have d : b ∣ (b - 1) ^ (b - 1) + (b ^ 2 - 1) ^ (b ^ 2 - 1) := by
    use (k*b)
    rw [hk]
    ring
  zify at d
  have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (b - 1)  = b-1 := by omega
  rw [this] at d
  have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (b ^ 2 - 1) = b^2 - 1 := by 
    refine LucasLehmer.Int.natCast_pow_pred b 2 ?_
    omega
  rw [this] at d

  by_contra nbe2
  have bge3: 3 ≤ b := by omega
  
  --We apply lemmas l1 and l2 and the discuss the parity of b.
  have t1 : (↑b - 1) ^ (b - 1) + (↑b ^ 2 - 1) ^ (b ^ 2 - 1) ≡ 0 [ZMOD (b:ℤ)] := by
    exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int d)

  --Odd b. Then s2b ≡ 2 [mod b], so b has to be 2 but there is no such choice.
  by_cases ob : Odd b
  have t2 : (↑b - 1) ^ (b - 1) ≡ 1 [ZMOD (b:ℤ)] := by 
    have a1: (↑b - 1) ^ (b - 1) ≡ (-1)^(b-1) [ZMOD (b:ℤ)] := by
      refine Int.ModEq.pow (b - 1) ?_
      apply l1 b
    have a2 : (-1)^(b-1) = 1 := by
      refine Even.neg_one_pow ?_
      refine Nat.Odd.sub_odd ob ?_
      norm_num
    rw [a2] at a1
    exact a1
  have t3 : (↑b ^ 2 - 1) ^ (b ^ 2 - 1) ≡ 1 [ZMOD (b:ℤ)] := by 
    have a1: (↑b^2 - 1) ^ (b^2 - 1) ≡ (-1)^(b^2-1) [ZMOD (b:ℤ)] := by
      refine Int.ModEq.pow (b ^ 2 - 1) ?_
      apply l2 b
    have a2 : (-1)^(b^2-1) = 1 := by
      refine Even.neg_one_pow ?_
      have ob2 : Odd (b^2) := by exact Odd.pow ob
      refine Nat.Odd.sub_odd ob2 ?_
      norm_num
    rw [a2] at a1
    exact a1
  have t4 : (↑b - 1) ^ (b - 1) + (↑b ^ 2 - 1) ^ (b ^ 2 - 1) ≡ 1+1 [ZMOD (b:ℤ)] := by exact Int.ModEq.add t2 t3
  simp at t4
  have t5 : 0 ≡ 2 [ZMOD (b:ℤ)] := by exact Int.ModEq.trans (id (Int.ModEq.symm t1)) t4
  have t6 : (b:ℤ) ∣ 2-0 := by exact Int.dvd_sub_of_emod_eq (id (Int.ModEq.symm t5))
  simp at t6; norm_cast at t6
  have : b ≤ 2 := by apply Nat.le_of_dvd; norm_num; exact t6
  linarith

  --Even b. Then s2b ≡ -2 [mod b], so b equals 2.
  have eb : Even b := by exact Nat.not_odd_iff_even.mp ob
  have t2 : (↑b - 1) ^ (b - 1) ≡ -1 [ZMOD (b:ℤ)] := by
    have a1: (↑b - 1) ^ (b - 1) ≡ (-1)^(b-1) [ZMOD (b:ℤ)] := by
      refine Int.ModEq.pow (b - 1) ?_
      apply l1 b
    have a2 : (-1)^(b-1) = -1 := by
      refine Odd.neg_one_pow ?_
      refine Nat.Even.sub_odd ?_ eb ?_
      linarith
      norm_num
    rw [a2] at a1
    exact a1
  have t3 : (↑b ^ 2 - 1) ^ (b ^ 2 - 1) ≡ -1 [ZMOD (b:ℤ)] := by
    have a1: (↑b^2 - 1) ^ (b^2 - 1) ≡ (-1)^(b^2-1) [ZMOD (b:ℤ)] := by
      refine Int.ModEq.pow (b ^ 2 - 1) ?_
      apply l2 b
    have a2 : (-1)^(b^2-1) = -1 := by
      refine Odd.neg_one_pow ?_
      have eb2 : Even (b^2) := by refine (Nat.even_pow' ?_).mpr eb; norm_num
      refine Nat.Even.sub_odd ?_ eb2 ?_
      nlinarith
      norm_num
    rw [a2] at a1
    exact a1
  have t4 : (↑b - 1) ^ (b - 1) + (↑b ^ 2 - 1) ^ (b ^ 2 - 1) ≡ -1+ (-1) [ZMOD (b:ℤ)] := by exact Int.ModEq.add t2 t3
  simp at t4
  have t5 : 0 ≡ -2 [ZMOD (b:ℤ)] := by exact Int.ModEq.trans (id (Int.ModEq.symm t1)) t4
  have t6 : (b:ℤ) ∣ 0-(-2) := by exact Int.ModEq.dvd (id (Int.ModEq.symm t5))
  simp at t6; norm_cast at t6
  have : b ≤ 2 := by apply Nat.le_of_dvd; norm_num; exact t6
  linarith


  --From right to left. Assume b=2, we can check directly that it works.
  intro be
  simp [be]
  norm_num
