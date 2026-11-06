import Mathlib

/-E37

Let $k$ be an integer greater than 3. Suppose that $A$, $B$, and $C$ are non-zero distinct digits less than $k$.
Suppose we have the following two equations in base $k$:

1) ${AB_k}+{C_k}={C0_k}$
2) ${AB_k}+{BA_k}={CC_k}$

(Interpret $XY_k$ as the number $X \cdot k + Y$. Interpret $X_k$ as the number $X$. Interpret $X0_k$ as the number $X \cdot k + 0$. Interpret $XX_k$ as the number $X \cdot k + X$.)

Determine the value of the base-10 expression $100A+10B+C$. Show the answer is $101k-191$.-/

theorem number_theory_638898 (k A B C: ℤ) (h1: 3 < k) (h2: 0 < A) (h3: 0 < B)
 (h7: C < k) (h11: A * k + B + C = C * k) (h12: A * k + B + B * k + A = C * k + C)
 : 100 * A + 10 * B + C = 101 * k - 191 := by
   suffices A = k - 2 ∧ B = 1 ∧ C = k - 1 by
      simp [this]
      ring
   replace h12: A = 2 * C - B * k := by
      clear *- h11 h12
      omega
   have lb: B < 2 := by
      by_contra! l
      have c: A ≤ 0 := by
         rw [h12]
         nlinarith
      linarith
   have vb: B = 1 := by
      omega
   simp [vb] at *
   have lc: k - 2 < C := by
      by_contra! l
      simp [h12] at h11
      replace h11: C * k + C + 1 = k ^ 2 := by
         clear *- h11
         nlinarith
      nlinarith
   have vc: C = k - 1 := by
      clear *- lc h7
      omega
   simp [vc] at h12
   simp [h12, vc]
   omega