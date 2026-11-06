import Mathlib

/-Let $b$ be an integer greater than 7. Let $x_1$ be the number whose representation in base $b$ is given by the list of digits $[4,3,2,1]$ in little-endian order (i.e., $x_1 = 4 \cdot b^0 + 3 \cdot b^1 + 2 \cdot b^2 + 1 \cdot b^3$). Let $x_2$ be the number whose representation in base $b$ is given by the list of digits $[1,4,3,2]$ in little-endian order (i.e., $x_2 = 1 \cdot b^0 + 4 \cdot b^1 + 3 \cdot b^2 + 2 \cdot b^3$). Evaluate $x_1+x_2$ and express the sum in base $b$. Show that the list of digits of $x_1+x_2$ in base $b$, in little-endian order, is $[5,7,5,3]$.-/

theorem number_theory_635175 {b x1 x2 : ℕ} 
    (hb : 7 < b)
    (hx1 : b.digits x1 = [4, 3, 2, 1])
    (hx2 : b.digits x2 = [1, 4, 3, 2]):
    b.digits (x1 + x2) = [5, 7, 5, 3] := by
    /-wirte x1 as x1 = 4 + 3b + 2b^2 + b^3-/
    replace hx1 : x1 = 4 + 3 * b + 2 * b^2 + b^3 := by  
      rw [← Nat.ofDigits_digits b x1]
      simp [Nat.ofDigits, hx1]
      linarith
    /-write x2 as x2 = 1 + 4b + 3b^2 + 2b^3-/
    replace hx2 : x2 = 1 + 4 * b + 3 * b^2 + 2 * b^3 := by
      rw [← Nat.ofDigits_digits b x2]
      simp [Nat.ofDigits, hx2]
      linarith
    /-write x1 + x2-/
    have hsum : x1 + x2 = 5 + 7 * b + 5 * b^2 + 3 * b^3 := by
      rw [hx1, hx2]
      linarith
    /-change the form of x1 + x2 and judge the coefficients is less than b-/
    replace hsum : x1 + x2 = 5 + b * (7 + b * (5 + b * (3 + b * 0))) := by linarith
    rw [hsum]
    repeat rw [Nat.digits_add]
    simp_all
    all_goals norm_num
    all_goals nlinarith