import Mathlib

/- Find the absolute value of the difference of the solutions of $x^2-5x+5=0$.-/
theorem algebra_10244 (x1 x2 : ℝ) (hx1 : x1^2-5*x1+5=0) (hx2 : x2^2-5*x2+5=0)
    (hx12 : x1≠x2) :
    |x1-x2| = Real.sqrt 5 := by
    rw [← one_mul (x1 ^ 2)] at hx1
    rw [show  1 * x1 ^ 2 - 5 * x1 + 5 = 1 * x1 * x1 + (-5) * x1 + 5  by ring_nf, mul_assoc] at hx1
    --Let the roots of this polynomial be $r_1$ and $r_2$. Since the sum of the roots of a polynomial $ax^2+bx+c=0$ is $-\frac{b}{a}$ and the product of the roots is $\frac{c}{a}$, $r_1+r_2=5$ and $r_1r_2=5$. Squaring the first equation results in $r_1^2+2r_1r_2+r_2^2=25$.
    have hx1d : discrim 1 (-5) 5 = (2 * 1 * x1 + -5) * (2 * 1 * x1 + -5)  := by
      rw [← sq]
      apply discrim_eq_sq_of_quadratic_eq_zero hx1
    have  h1 :  (1 : ℝ) ≠ 0 := by simp
    rw [← hx1d] at hx1d; nth_rewrite 2[discrim] at hx1d; ring_nf at hx1d
    --Notice that $(r_1-r_2)^2=r_1^2-2r_1r_2+r_2^2$, so the difference of the roots can be obtained by subtracting 4 copies of the product of the roots from the square of their sum: $r_1^2-2r_1r_2+r_2^2=r_1^2+2r_1r_2+r_2^2-4r_1r_2=25-4(5)=5$. Therefore, $|r_1-r_2|=\boxed{\sqrt{5}}$.
    have s5 : √5 * √5  =5 := by simp
    nth_rewrite 3[← s5] at hx1d
    have hxeq := quadratic_eq_zero_iff h1 hx1d
    rw [hxeq] at hx1; simp at hx1
    rw [show   x2 ^ 2 - 5 * x2 + 5 = 1 * x2 * x2 + (-5) * x2 + 5  by ring_nf] at hx2
    rw [mul_assoc, hxeq] at hx2; simp at hx2
    have h5 : (0 : ℝ) < 5 := by simp
    --We also could have used the quadratic formula to determine that the roots are $\dfrac{5 \pm \sqrt{5}}{2}$, and the positive difference of these roots is indeed $\boxed{\sqrt{5}}$.
    cases hx1 with
    | inl h =>
      cases hx2 with
      | inl h2 =>
        rw [← h2] at h
        tauto
      | inr h2 =>
        rw [h,h2]; ring_nf;
        rw [abs_of_pos]
        apply Real.sqrt_pos_of_pos h5
    | inr h =>
      cases hx2 with
      | inl h2 =>
        rw [h,h2]; ring_nf; simp
      | inr h2 =>
        rw [← h2] at h
        tauto
