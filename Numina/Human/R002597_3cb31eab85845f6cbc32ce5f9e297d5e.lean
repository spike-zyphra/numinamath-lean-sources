import Mathlib

/- Participation in the local soccer league this year is 10% higher than last year. 
The number of males increased by 5% and the number of females increased by 20%. 
What fraction of the soccer league is now female?
(A) 1/3   (B) 4/11  (C) 2/5   (D) 4/9   (E) 1/2 -/
theorem algebra_96009 (x m f: ℕ) (h : x ≠ 0) (h1 : x = m + f)
(h2 : (Nat.cast x) * (1 + 10 / 100 : ℝ) = (Nat.cast m) * (1 + 5 / 100 : ℝ) + (Nat.cast f) * (1 + 20 / 100 : ℝ)) :
(Nat.cast f) * (1 + 20 / 100 : ℝ) / ((Nat.cast x)  * (1 + 10 / 100 : ℝ)) = 4 / 11 := by
--simplify the equation to a linear one
field_simp
ring_nf
--substitute m = x - f to have an equation in terms of f and x
have hh: m = x - f := by exact Nat.eq_sub_of_add_eq (id (Eq.symm h1))
rw[hh] at h2
--solve the equation to find the thesis with several algebraic passages
field_simp at h2
ring_nf at h2
have hhh: f ≤ x := by calc
  f ≤ m + f := by exact Nat.le_add_left f m
  _ = x := by exact id (Eq.symm h1)
rw[Nat.cast_sub hhh] at h2
ring_nf at h2
have hf : (x:ℝ) * 110 - (x:ℝ) * 105 = (f:ℝ) * 15 := by exact sub_eq_of_eq_add' h2
ring_nf at hf
have hff : 88 * ((x:ℝ) * 5) = 88 * ((f:ℝ) * 15) := by exact congrArg (HMul.hMul 88) hf
ring_nf at hff
exact id (Eq.symm hff)