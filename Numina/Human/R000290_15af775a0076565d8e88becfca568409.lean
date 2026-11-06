import Mathlib


/-
The expressions  $A=1\times2+3\times4+5\times6+\cdots+37\times38+39$  and  $B=1+2\times3+4\times5+\cdots+36\times37+38\times39$  are obtained by writing multiplication and addition operators in an alternating pattern between successive integers. Find the positive difference between integers  $A$  and  $B$ .
-/

theorem number_theory_8832
    (A B : ℤ)
    (hdefA : A = (∑ i ∈ Finset.range 19, (((2:ℤ) * i + 1) * (2 * i + 2))) + 39)
    (hdefB : B = 1 + (∑ i ∈ Finset.range 19, ((2:ℤ) * i + 2) * (2 * i + 3))) :
    |A - B| = 722 := by

  -- Just write in terms and eventually do some stuff to get $2\cdot(2+4+6+8\dots+38)$ . Sum of the first  $n$  even numbers is  $n(n+1)$  so we do  $2\cdot19\cdot20$  and get 760. But then we have  $1-39=-38$  so we subtract  $38$  to get an answer of 722 $

  have : A - B = -722 := by
    calc A - B
      _ = 39 - 1 + (∑ i ∈ Finset.range 19, (((2:ℤ) * i + 1) * (2 * i + 2) - (2 * i + 2) * (2 * i + 3))) := by
        rw [hdefA, hdefB]
        ring
      _ = 38 + ∑ i ∈ Finset.range 19, 2 * ((-2 : ℤ) * (i + 1)) := by ring
      _ = -722 := by ring

  norm_num [this]
