import Mathlib

/- 10. Given that $a, b, 2$ are the side lengths of a triangle, and $a, b$ are the roots of the equation
$$
\left(3 x^{2}-4 x-1\right)\left(3 x^{2}-4 x-5\right)=12
$$

the perimeter of the triangle can only be ( ).
(A) $\frac{10}{3}$ or $\frac{8}{3}$
(B) $\frac{14}{3}$ or $\frac{10}{3}$
(C) $\frac{16}{3}$ or $\frac{14}{3}$
(D) $\frac{16}{3}$ or $\frac{20}{3}$ -/
theorem algebra_296571 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (3 * a ^ 2 - 4 * a - 1) * (3 * a ^ 2 - 4 * a - 5) = 12)
    (h' : (3 * b ^ 2 - 4 * b - 1) * (3 * b ^ 2 - 4 * b - 5) = 12)
    (h'' : a + b > 2) (h''' : a + 2 > b) (h'''' : b + 2 > a) :
    a + b + 2 = 16 / 3 ∨ a + b + 2 = 20 / 3 := by
  have (x : ℝ) (hx : (3 * x ^ 2 - 4 * x - 1) * (3 * x ^ 2 - 4 * x - 5) = 12) :
      x = -1 ∨ x = 7 / 3 ∨ x = 1 ∨ x = 1 / 3 := by
    -- From $\left(3 x^{2}-4 x\right)^{2}-6\left(3 x^{2}-4 x\right)-7=0$, we get $\left(3 x^{2}-4 x-7\right)\left(3 x^{2}-4 x+1\right)=0$.
    replace hx : (3 * x ^ 2 - 4 * x - 7) * (3 * x ^ 2 - 4 * x + 1) = 0 := by
      rw [← sub_eq_zero] at hx
      ring_nf at hx
      ring_nf
      exact hx
    -- Solving, we find $x_{1}=-1, x_{2}=\frac{7}{3}, x_{3}=1, x_{4}=\frac{1}{3}$.
    rw [mul_eq_zero] at hx
    obtain (hx | hx) := hx
    · replace hx : (x - -1) * (3 * x - 7) = 0 := by
        ring_nf at hx
        ring_nf
        exact hx
      rw [mul_eq_zero, sub_eq_zero, sub_eq_zero, mul_comm, ← eq_div_iff_mul_eq (by norm_num)] at hx
      obtain (hx | hx) := hx <;> simp [hx]
    · replace hx : (x - 1) * (3 * x - 1) = 0 := by
        ring_nf at hx
        ring_nf
        exact hx
      rw [mul_eq_zero, sub_eq_zero, sub_eq_zero, mul_comm, ← eq_div_iff_mul_eq (by norm_num)] at hx
      obtain (hx | hx) := hx <;> simp [hx]
  replace h := this a h
  replace h' := this b h'
  -- From $a+b > 2,|a-b| < 2$, we know $a=b=\frac{7}{3}$ or $a=\frac{7}{3}, b=1$ or $a=1, b=\frac{7}{3}$.
  have hab : a > 1 ∨ b > 1 := by
    by_contra!
    linarith
  replace hab : a = 7 / 3 ∨ b = 7 / 3 := by
    apply hab.imp
    · intro ha
      contrapose! h
      split_ands
      · linarith
      · assumption
      · linarith
      · linarith
    · intro hb
      contrapose! h'
      split_ands
      · linarith
      · assumption
      · linarith
      · linarith
  replace hab : a = 7 / 3 ∧ b = 7 / 3 ∨ a = 7 / 3 ∧ b = 1 ∨ a = 1 ∧ b = 7 / 3 := by
    obtain (rfl | rfl) := hab
    · simp; norm_num
      contrapose! h'
      split_ands
      · linarith
      · exact h'.1
      · exact h'.2
      · linarith
    · simp; norm_num
      contrapose! h
      split_ands
      · linarith
      · exact h.1
      · exact h.2
      · linarith
  -- Thus, the perimeter of the triangle is $\frac{16}{3}$ or $\frac{20}{3}$.
  obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hab <;> norm_num
