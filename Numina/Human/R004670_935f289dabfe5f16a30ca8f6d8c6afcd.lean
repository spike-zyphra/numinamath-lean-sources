import Mathlib

/-
6. Let $a$, $b$, $c$ be three prime numbers, and satisfy $a b c=5(a+b+c)$.
Then these three numbers in ascending order are $\qquad$
-/

theorem number_theory_296670 (a b c : ℕ)(ha: Nat.Prime a) (hb: Nat.Prime b) (hc: Nat.Prime c) (hab: a≤b) (hbc: b≤c):
(a*b*c = 5 * (a+b+c)) ↔ (a=2 ∧ b=5 ∧ c=7) := by
  
  constructor

  --From left to right.
  intro h

  have age2 : 2 ≤ a := by exact Nat.Prime.two_le ha
  have bge2 : 2 ≤ b := by exact Nat.Prime.two_le hb
  have cge2 : 2 ≤ c := by exact Nat.Prime.two_le hc
  
  --By our assumption, we have 5 ∣ a*b*c, so one of them is 5.
  have d5: 5 ∣ a*b*c := by use (a+b+c)
  have p5 : Nat.Prime 5 := by norm_num
  have : 5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c := by
    by_cases ad5 : 5 ∣ a 
    left
    exact ad5
    
    have : Nat.Coprime 5 a := by exact (Nat.Prime.coprime_iff_not_dvd p5).mpr ad5
    rw [mul_assoc] at d5
    have : 5 ∣ b*c := by 
      rw [Nat.Coprime.dvd_mul_left] at d5
      exact d5
      exact this
    have : 5 ∣ b ∨ 5 ∣ c := by exact (Nat.Prime.dvd_mul p5).mp this
    tauto

  --We enumerate which one is 5 and solve the equations. The only possible solution is a = 2, b = 5, and c = 7.
  obtain d5a | d5b | d5c := this
  have ae : a = 5 := by 
    rw [Nat.Prime.dvd_iff_eq] at d5a; 
    exact d5a; 
    exact ha
    norm_num
  have : (b-1)*(c-1) = 6 := by 
    rw [ae] at h
    nlinarith
  have ddd: (b-1) ∣ 6 := by use c-1; omega
  have d6mem: Nat.divisors 6 = {1, 2, 3, 6}:= by decide
  have : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 7 := by
    have : (b-1) ∈ Nat.divisors 6 := by 
      refine Nat.mem_divisors.mpr ?_
      simp; exact ddd
    rw [d6mem] at this
    simp at this ⊢
    exact this
  rcases this with b2 | b3 | b4 | b7
  linarith
  linarith
  linarith
  have : c = 2 := by rw [b7] at this; simp at this; omega
  linarith
  
  have be : b = 5 := by 
    rw [Nat.Prime.dvd_iff_eq] at d5b; 
    exact d5b; 
    exact hb
    norm_num
  have : (a-1)*(c-1) = 6 := by 
    rw [be] at h
    ring_nf at h ⊢
    rify at h ⊢
    field_simp at h ⊢
    ring_nf at h ⊢
    nlinarith
  have ddd: (a-1) ∣ 6 := by use (c-1); omega
  have d6mem: Nat.divisors 6 = {1, 2, 3, 6}:= by decide
  have : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7 := by
    have : (a-1) ∈ Nat.divisors 6 := by
      refine Nat.mem_divisors.mpr ?_
      simp; exact ddd
    rw [d6mem] at this
    simp at this ⊢
    exact this
  rcases this with a2 | a3 | a4 | a7
  have ce : c = 7:= by simp [a2] at this; exact this
  tauto
  have ce : c = 4:= by simp [a3] at this; omega
  rw [ce] at hc; norm_num at hc
  rw [a4] at ha; norm_num at ha
  linarith

  have ce : c = 5 := by 
    rw [Nat.Prime.dvd_iff_eq] at d5c; 
    exact d5c; 
    exact hc
    norm_num
  have : (a-1)*(b-1) = 6 := by 
    simp [ce] at h
    rify at h ⊢
    ring_nf at h ⊢
    field_simp at h ⊢
    ring_nf at h ⊢
    nlinarith
  have ddd: (a-1) ∣ 6 := by use (b-1); omega
  have d6mem: Nat.divisors 6 = {1, 2, 3, 6}:= by decide
  have : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7 := by
    have : (a-1) ∈ Nat.divisors 6 := by
      refine Nat.mem_divisors.mpr ?_
      simp; exact ddd
    rw [d6mem] at this
    simp at this ⊢
    exact this
  rcases this with a2 | a3 | a4 | a7
  have be : b = 7 := by simp [a2] at this; exact this
  linarith
  have be : b = 4 := by simp [a3] at this; omega
  rw [be] at hb; norm_num at hb
  rw [a4] at ha; norm_num at ha
  linarith

  --From right to left. Simple calculation.
  intro ⟨ae,be,ce⟩
  simp [ae,be,ce]