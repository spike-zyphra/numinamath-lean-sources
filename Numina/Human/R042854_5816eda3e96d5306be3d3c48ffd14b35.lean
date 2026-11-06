import Mathlib

/-
1.1. The product of 3 integer numbers is -5. What values can their sum take? Be sure to list all options.
-/

theorem number_theory_108828 : {a + b + c | (a : ℤ) (b : ℤ) (c : ℤ) (h : a * b * c = -5)} = {5,-3,-7} := by
  ext x
  simp

  constructor
  intro h
  
  obtain ⟨a,b,c,h, hs⟩ := h
  
  --Since the product is -5, at least one of a,b,c is negative. Assue that a < 0.
  wlog ha: a<0
  have hbc: b < 0 ∨ c < 0 := by
    push_neg at ha
    by_contra bpcp
    push_neg at bpcp
    obtain ⟨bp, cp⟩ := bpcp
    have : 0 ≤ a * b * c := by positivity
    linarith
  obtain bn | cn := hbc
  apply this x b a c
  nlinarith
  linarith
  exact bn
  apply this x c a b
  nlinarith
  linarith
  exact cn

  --Then, a can only be -1 or -5.
  let a' : ℕ := (-a).toNat
  have : a' = -a := by simp [a']; linarith
  have eqp: a' * b * c = 5:= by rw [this]; linarith
  have : 0 < b*c := by nlinarith
  have apd: a' ∣ 5 := by 
    use (b*c).toNat;
    have : (b*c).toNat = b * c := by simp; linarith
    zify
    rw [this]
    symm;
    ring_nf
    exact eqp
  have p5: Nat.Prime 5 := by norm_num
  have : a' = 1 ∨ a' = 5 := by exact (Nat.dvd_prime p5).mp apd
  
  --We consider each case respectively.
  rcases this with apeq | ape5
  --Case a=-1.  Then, bc=5. The possible pairs of (b,c) are (1,5),(5,1),(-1,-5),(-5,-1).
  have ae : a = -1 := by linarith
  rw [ae] at h; field_simp at h
  by_cases bp : 0 < b
  
  have : 0 < c := by nlinarith
  let b':ℕ := b.toNat
  let c':ℕ := c.toNat
  have tb: b' = b := by simp [b']; linarith
  have tc: c' = c := by simp [c']; linarith
  have bpd5: b' ∣ 5 := by use c'; zify; rw [tb,tc]; linarith
  have : b' = 1 ∨ b' = 5 := by exact (Nat.dvd_prime p5).mp bpd5
  rcases this with bp1 | bp5
  have be: b = 1 := by linarith
  have ce: c = 5 := by nlinarith
  rw [ae,be,ce] at hs
  field_simp at hs
  tauto
  have be: b = 5 := by linarith
  have ce: c = 1 := by nlinarith
  rw [ae,be,ce] at hs
  field_simp at hs
  tauto

  have : b < 0 := by 
    by_contra bnneq
    push_neg at bnneq bp
    have : b = 0:= by exact Eq.symm (Int.le_antisymm bnneq bp)
    rw [this] at h; norm_num at h
  have : c < 0 := by nlinarith
  let b':ℕ := (-b).toNat
  let c':ℕ := (-c).toNat
  have tb: b' = -b := by simp [b']; linarith
  have tc: c' = -c := by simp [c']; linarith
  have bpd5: b' ∣ 5 := by use c'; zify; rw [tb,tc]; linarith
  have : b' = 1 ∨ b' = 5 := by exact (Nat.dvd_prime p5).mp bpd5
  rcases this with bp1 | bp5
  have be: b = -1 := by linarith
  have ce: c = -5 := by nlinarith
  rw [ae,be,ce] at hs
  ring_nf at hs
  tauto
  have be: b = -5 := by linarith
  have ce: c = -1 := by nlinarith
  rw [ae,be,ce] at hs
  ring_nf at hs
  tauto

  --Case a=-5. Then, bc=1. The possible pairs of (b,c) are (1,1),(-1,-1).
  have ae: a = -5 := by linarith
  rw [ape5] at eqp
  ring_nf at eqp
  field_simp at eqp
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at eqp
  rcases eqp with ⟨be,ce⟩ | ⟨be,ce⟩ 
  rw [ae,be,ce] at hs;
  simp at hs
  tauto
  rw [ae,be,ce] at hs;
  simp at hs
  tauto

  --Simple calculation to show that all three numbers are possible.
  intro h
  rcases h with (h | h | h)
  
  use 1, -1, 5
  simp [h]

  use 1, 1, -5
  simp [h]

  use -1, -1, -5
  simp [h]

