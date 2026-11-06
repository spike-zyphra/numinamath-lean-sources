import Mathlib


/-- Find all integer solutions of the following system of linear Diophantine equations:
a)
$$
\begin{array}{l}
x+y+z=100 \\
x+8y+50z=156
\end {array}
$$-/
theorem number_theory_4632_a (x y z : ℤ) (h1 : x + y + z = 100)
  (h2 : x + 8 * y + 50 * z = 156) : ∃ n, z = n ∧ y = 8 - 7 * n ∧ x = 92 + 6 * z := by
    have h4 : y = 8 - 7 * z := by linarith
    have h5 : x = 92 + 6 * z := by linarith
    exact ⟨z, ⟨rfl, ⟨h4, h5⟩⟩⟩

/-- Find all integer solutions of the following systems of linear Diophantine equations:
b)
$$\begin{array}{l}
x+y+z=100 \\
x+6y+21z=121
\end{array}$$-/
theorem number_theory_4632_b (x y z : ℤ) (h1 : x + y + z = 100)
  (h2 : x + 6 * y + 21 * z = 121) : False := by
    have h3 : 5 * y + 20 * z = 21 := by linarith
    have h4 : 5 * y + 20 * z ≡ 21 [ZMOD 5] := congrFun (congrArg HMod.hMod h3) 5
    have h5 : 5 * y ≡ 0 [ZMOD 5] := Dvd.dvd.modEq_zero_int (Int.dvd_mul_right 5 y)
    have h6 : 20 * z ≡ 0 [ZMOD 5] := Dvd.dvd.modEq_zero_int (Dvd.dvd.mul_right (by decide) z)
    have h7 : 5 * y + 20 * z ≡ 0 [ZMOD 5] := Int.ModEq.add h5 h6
    have := h7.symm.trans h4
    tauto

/-- Find all integer solutions of the following systems of linear Diophantine equations:
c)
$$\begin{array}{l}
x+y+z+w=100 \\
x+2y+3z+4w=300 \\
x+4y+9z+16w=1000
\end{array}$$-/
theorem number_theory_4632_c (x y z w : ℤ) (h1 : x + y + z + w = 100)
  (h2 : x + 2 * y + 3 * z + 4 * w = 300)
  (h3 : x + 4 * y + 9 * z + 16 * w = 1000)
    : ∃ n, w = n ∧ z = 150 - 3 * n ∧ y = -100 + 3 * n ∧ x = 50 - n :=
      ⟨w, ⟨rfl, ⟨by linarith, ⟨by linarith, by linarith⟩⟩⟩ ⟩
