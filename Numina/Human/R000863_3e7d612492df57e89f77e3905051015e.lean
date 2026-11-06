import Mathlib
/- A square is drawn such that one of its sides coincides with the line $y = 7$, and so that the endpoints of this side lie on the parabola $y = 2x^2 + 8x + 4$. What is the area of the square?-/
theorem algebra_18692 (P Q : ℝ × ℝ)
    (hP : 2 * P.1 ^ 2 + 8 * P.1 + 4 = 7) (hQ : 2  * Q.1 ^ 2 + 8 * Q.1 + 4 = 7)
    (hPQ :2 * P.2 = 2 * P.1 ^ 2 + 8 * P.1 + 4) (hP'Q' : Q.2 = 2 * Q.1 ^ 2 + 8 * Q.1 + 4)
    (hP'Q : P.1 ≠ Q.1) :
    (P.1 - Q.1)^2 = 22 := by
    --The points of intersection of the line $y = 7$ and $y = 2x^2 + 8x + 4$, by substitution, are found when $2x^2 + 8x + 4 = 7 \Longrightarrow 2x^2 + 8x - 3 = 0$.
    have e := congrArg ( fun (n) => ((n) - 7) ) hP ; simp at e
    rw [show 2 * P.1 ^ 2 + 8 * P.1 + 4 - 7 = 2 *  P.1 * P.1 + 8 * P.1  + (- 3) by ring_nf] at e
    have hd : discrim (2 : ℝ ) 8 (-3) =  (2 * 2 * P.1 + 8) ^ 2 := by
      apply discrim_eq_sq_of_quadratic_eq_zero _
      ring_nf at *
      assumption
    rw [show (2 * 2 * P.1 + 8) ^ 2 = (2 * 2 * P.1 + 8) * (2 * 2 * P.1 + 8)  by ring_nf] at hd
    have ha :  (2 : ℝ ) ≠ 0 := by linarith
    rw [← hd] at hd; nth_rewrite 2[discrim] at hd; ring_nf at hd
    have s88 : √88 * √88  = 88 := by simp
    rw [← s88] at hd
    --By the quadratic formula, $$x = \frac{-8 \pm \sqrt{8^2 - 4 \cdot 2 \cdot (-3)}}{2 \cdot 2}.$$We want to find the difference of these roots to find the difference of the x-coordinates of the point of intersection, which will give a side length of the square. The difference is given by $\frac{\sqrt{8^2 - 4 \cdot 2 \cdot (-3)}}2 = \frac{\sqrt{88}}{2} = \sqrt{22}$. Thus, the area of the square is $\boxed{22}$.
    have heq := quadratic_eq_zero_iff  ha hd
    rw [mul_assoc, heq] at e
    have e2 := congrArg ( fun (n) => ((n) - 7) ) hQ; simp at e2
    rw [show 2 * Q.1 ^ 2 + 8 * Q.1 + 4 - 7 = 2 *  Q.1 * Q.1 + 8 * Q.1  + (- 3) by ring_nf] at e2
    have heq2 := quadratic_eq_zero_iff  ha hd
    rw [mul_assoc, heq2] at e2
    ring_nf at e
    ring_nf at e2
    cases e with
    | inl h =>
      cases e2 with
      | inl h2 =>
        rw [← h2] at h
        tauto
      | inr h2 =>
        rw [h];rw [h2]
        ring_nf
        rw [Real.sq_sqrt]
        ring_nf
        linarith
    | inr h =>
      cases e2 with
      | inl h2 =>
        rw [h];rw [h2]
        ring_nf
        rw [Real.sq_sqrt]
        ring_nf
        linarith
      | inr h2 =>
        rw [← h2] at h
        tauto
