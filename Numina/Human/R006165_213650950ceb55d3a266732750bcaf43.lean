import Mathlib

/-
If $a$, $b$, $c$, $d$ are non-negative integers, and $\left( {{a}^{2}}+{{b}^{2}} \right)\left( {{c}^{2}}+{{d}^{2}} \right)=1993$, then $a+b+c+d=$ ___          ___ .
-/

theorem number_theory_627254 (a b c d : ℕ) (h: (a^2+b^2)*(c^2+d^2) = 1993): a + b + c + d = 56 := by
  
  --Wlog, we can assume that a^2+b^2 ≤ c^2+d^2, a≤b, and c ≤ d.
  wlog ablecd: (a^2+b^2) ≤ c^2+d^2
  have re: c^2 + d^2 ≤ a^2 + b^2 := by linarith
  have : c + d + a + b = 56 := by 
    apply this
    exact re
    nlinarith 
  linarith
  wlog aleb : a ≤ b
  have blea : b ≤ a := by omega
  have : b + a + c + d = 56 := by 
    apply this
    linarith
    linarith
    exact blea
  linarith
  wlog cled : c ≤ d
  have dlec : d ≤ c := by omega
  have : a + b + d + c = 56 := by
    apply this
    linarith
    linarith
    exact aleb
    exact dlec
  linarith

  --Then, note that 1993 is a prime. We have c^2+d^2 = 1993 or 1.
  have mydv: (c^2+d^2) ∣ 1993 := by use (a^2+b^2); linarith
  have p1993 : Nat.Prime 1993 := by norm_num
  have : c^2+d^2 = 1 ∨ c^2+d^2 = 1993 := by exact (Nat.dvd_prime p1993).mp mydv
  rcases this with cd1 | cd1993
  
  --The case c^2 + d^2 = 1. It is not possible because then a^2+d^2 = 1993 > c^2 + d^2.
  have : a^2 + b^2 = 1993 := by rw [cd1] at h; norm_num at h; exact h
  linarith

  --The case c^2 + d^2 = 1993.
  have a2b2: a^2 + b^2 = 1 := by rw [cd1993] at h; norm_num at h; exact h
  have : 0 ≤ a^2 := by exact sq_nonneg a
  have : a^2 ≤ 1 := by nlinarith
  by_cases a2: a^2 = 1
  have : a = 1 := by exact Nat.eq_one_of_mul_eq_one_left a2
  have : b = 0 := by rw [this] at a2b2; norm_num at a2b2; exact a2b2
  linarith
  have ae: a^2 = 0 := by omega
  simp at ae
  have be: b = 1 := by nlinarith

  --We enumerate the possible values for d.
  have : 31 < d := by nlinarith
  have : d ≤ 44 := by nlinarith

  by_cases de : d = 32
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 969 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 969 := by native_decide
  apply t2 at t1; exact t1

  by_cases de : d = 33
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 904 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 904 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 34
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 837 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 837 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 35
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 768 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 768 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 36
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 697 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 697 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 37
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 624 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 624 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 38
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 549 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 549 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 39
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 472 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 472 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 40
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 393 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 393 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 41
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 312 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 312 := by native_decide
  apply t2 at t1; exact t1
  
  by_cases de : d = 42
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 229 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 229 := by native_decide
  apply t2 at t1; exact t1
 
  by_cases de : d = 43
  rw [de] at cd1993
  norm_num at cd1993
  have ce: c = 12 := by nlinarith
  rw [ae,be,ce,de]

  have de : d = 44 := by omega
  exfalso;
  rw [de] at cd1993
  norm_num at cd1993
  simp at cd1993
  have t1: IsSquare 57 := by use c; ring_nf; symm; exact cd1993
  have t2: ¬ IsSquare 57 := by native_decide
  apply t2 at t1; exact t1
