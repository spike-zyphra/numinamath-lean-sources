import Mathlib

 /- 8. (10 points) Given $n!=1 \times 2 \times 3 \times \cdots \times n$, what is the result of the expression $\frac{(2014!-1)!\times 2015!}{(2014!)!}$? $\qquad$ . -/
theorem number_theory_266457 : Nat.factorial (Nat.factorial 2014 - 1) * Nat.factorial 2015 / Nat.factorial (Nat.factorial 2014) = 2015 := by
  have := Nat.factorial_succ 2014
  simp at this
  rw [this]
  have {a b c : ℕ} : a*(b*c)=(c*a)*b := by linarith
  rw [this]
  have : Nat.factorial 2014 ≥ 1 := Nat.factorial_pos 2014
  have h : Nat.factorial 2014 = Nat.factorial 2014 - 1 + 1 := (Nat.sub_add_cancel this).symm
  nth_rw 1 [h]
  rw [←Nat.factorial_succ (Nat.factorial 2014 - 1)]
  rw [←h]
  simp [Nat.factorial_pos (Nat.factorial 2014)]
