import Mathlib

/-
5) Simone writes the number 3 on the blackboard, then erases it and replaces it with its square, 9, then erases the 9 and replaces it with its square, 81. She repeats this operation a total of 2006 times: each time she replaces the written number with its square. What is the unit digit of the last number written?
(A) 1 ,
(B) $3, \quad$ (C) 5 ,
(D) $7, \quad$ (E) 9 .
-/

theorem number_theory_130118 (a: ℕ → ℕ) (ha0: a 0 = 3) (h: ∀ n, a (n+1) = (a n)^2):
(a 2006)%10 = 1 := by
  have ha1 : a 1 = 9 := by simp [ha0, h]
  have ha2 : a 2 = 81 := by simp [ha1, h]

  --For every n ≥ 2, the last digit of a n is 1, since a 2 % 10 = 1 and the units digits remain 1 forever.
  have cla : ∀n:ℕ, a (n+2) % 10 = 1 := by
    intro n
    induction' n with n hn

    simp [ha2]

    have : a (n+1+2) = a (n+2+1) := by ring
    rw [this]
    specialize h (n+2)
    rw [h]
    rw [Nat.pow_mod]
    rw [hn]
  
  specialize cla 2004
  norm_num at cla
  exact cla