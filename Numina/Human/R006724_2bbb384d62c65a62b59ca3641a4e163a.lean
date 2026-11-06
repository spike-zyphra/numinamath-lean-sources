import Mathlib

/-Let $b$ be an integer such that $b \ge 5$. A plumber charges an hourly rate for labor. This rate is given as the number $242_b$ (which denotes the value $2 \cdot b^2 + 4 \cdot b + 2$ in base 10). The plumber also charges a fixed fee for equipment. This fee is given as the number $367_8$ (which denotes the value $3 \cdot 8^2 + 6 \cdot 8 + 7$ in base 10). If the plumber works for $3.5$ hours, show that the total amount the plumber is owed, calculated in base 10, is $7(b+1)^2 + 247$.-/
theorem number_theory_640559 (b P F : ℕ) (hP : P = Nat.ofDigits b [2, 4, 2]) (hF : F = Nat.ofDigits 8 [7, 6, 3]) : 3.5 * (P : ℝ) + F = 7 * (b + 1)^2 + 247 := by
  have hF' : F = 247 := by
    rw [hF]
    rfl
  have hP' : P = 2 * b^2 + 4 * b + 2 := by
    simp only [hP, Nat.ofDigits, Nat.cast_ofNat, mul_zero, add_zero]
    ring_nf
  rw [hP', hF']
  norm_num
  ring_nf
