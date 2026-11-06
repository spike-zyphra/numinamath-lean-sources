import Mathlib

/- Suppose that $N$ can be written in base $6$ as $531340_6$ and in base $8$ as $124154_8$. In base $10$, what is the remainder when $N$ is divided by $210$? -/
theorem number_theory_22865 {N : ℕ} (hN6 : N = 5*6^5 + 3*6^4 + 1*6^3+3*6^2+4*6) (hN8 : N = 1*8^5+2*8^4+4*8^3+1*8^2+5*8+4) :
    N ≡ 66 [MOD 210] := by
  -- notice that 210 = 6x5x7. by chinese remainder theorem, it suffices to find N modulo 5,6,7. the last digit of N in base 6 is 0, so N module 6 is 0.
  have hm6: N ≡ 0 [MOD 6] := by
    have: N = 6*(5*6^4+3*6^3+1*6^2+3*6+4) := by
      rw [hN6]; ring
    rw [this]
    apply Nat.modEq_zero_iff_dvd.mpr
    apply Nat.dvd_mul_right 6
  -- and a (p+1)^n mod p is a.
  have h1(a n p:ℕ): a*(p+1)^n ≡ a [MOD p] := by
    have hh1: p+1 ≡ 1 [MOD p] := by
      exact Nat.add_modEq_left
    have hh2: (p+1)^n ≡ 1 [MOD p] := by
      have: 1 = 1^n := by simp
      nth_rw 2 [this]
      exact Nat.ModEq.pow n hh1
    nth_rw 2 [← mul_one a]
    exact Nat.ModEq.mul rfl hh2
  -- add mod, (a+b) mod p = a mod p + b mod p
  have hadd5{a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 p : ℕ}:
    a1 ≡ b1 [MOD p] → a2 ≡ b2 [MOD p] → a3 ≡ b3 [MOD p]
    → a4 ≡ b4 [MOD p] → a5 ≡ b5 [MOD p] →
    (a1+a2+a3+a4+a5) ≡ (b1+b2+b3+b4+b5) [MOD p] := by
    intro hh1 hh2 hh3 hh4 hh5
    apply Nat.ModEq.add ?_ hh5
    apply Nat.ModEq.add ?_ hh4
    apply Nat.ModEq.add ?_ hh3
    apply Nat.ModEq.add hh1 hh2
  -- so N mod 5 is 5+3+1+3+4 = 16
  have h2: N ≡ 16 [MOD 5] := by
    rw [hN6]
    have h6: 6 = 5+1 := by ring
    have hh1:  5*6^5 ≡ 5 [MOD 5] := by
      rw [h6]
      apply h1
    have hh2:  3*6^4 ≡ 3 [MOD 5] := by
      rw [h6]
      apply h1
    have hh3:  1*6^3 ≡ 1 [MOD 5] := by
      rw [h6]
      apply h1
    have hh4:  3*6^2 ≡ 3 [MOD 5] := by
      rw [h6]
      apply h1
    have hh5:  4*6 ≡ 4 [MOD 5] := by
      rw [← pow_one 6]
      rw [h6]
      apply h1
    have hh6: 16 = 5+3+1+3+4 := by ring
    rw [hh6]
    apply hadd5 hh1 hh2 hh3 hh4 hh5
  -- and N mod 7 is 17
  have h3: N ≡ 17 [MOD 7] := by
    rw [hN8]
    have hadd6{a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 p : ℕ}:
    a1 ≡ b1 [MOD p] → a2 ≡ b2 [MOD p] → a3 ≡ b3 [MOD p]
    → a4 ≡ b4 [MOD p] → a5 ≡ b5 [MOD p] → a6 ≡ b6 [MOD p] →
    (a1+a2+a3+a4+a5+a6) ≡ (b1+b2+b3+b4+b5+b6) [MOD p] := by
      intro hh1 hh2 hh3 hh4 hh5 hh6
      apply Nat.ModEq.add
      · apply hadd5 hh1 hh2 hh3 hh4 hh5
      · apply hh6
    have h8: 8 = 7+1 := by ring
    have h17: 17 = 1+2+4+1+5+4 := by ring
    rw [h8, h17]
    apply hadd6
    · apply h1
    · apply h1
    · apply h1
    · apply h1
    · rw [← pow_one (7+1)]
      apply h1
    · rfl
  -- notice that 16 ≡ 31 mod 5 and 17 ≡ 31 mod 7. so N ≡ 31 mod 35
  have h4: N ≡ 31 [MOD 35] := by
    have hh1: N ≡ 31 [MOD 5] := by
      apply Nat.ModEq.trans h2 rfl
    have hh2: N ≡ 31 [MOD 7] := by
      apply Nat.ModEq.trans h3 rfl
    have hh3: 35 = 5*7 := by ring
    rw [hh3]
    have hh4: Nat.Coprime 5 7 := by norm_num
    apply (Nat.modEq_and_modEq_iff_modEq_mul hh4).mp
    exact ⟨hh1,hh2⟩
  -- notice that 31 ≡ 66 mod 35 and 0 ≡ 66 mod 6. so N ≡ 66 mod 210.
  have hco: Nat.Coprime 35 6 := by norm_num
  have h5: 210 = 35 * 6 := by ring
  rw [h5]
  apply (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
  constructor
  · apply Nat.ModEq.trans h4 rfl
  · apply Nat.ModEq.trans hm6 rfl