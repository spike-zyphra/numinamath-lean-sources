import Mathlib

/-Given a quadratic function $f(x) = ax^2 + bx + c = 0$ ($a > 0$), it satisfies the relation $f(2+x) = f(2-x)$. Compare the size of $f(0.5)$ and $f(\pi)$.-/
theorem algebra_9466 {a b c : ℝ} (ha : a > 0)
  (h : ∀ x, a * (2 + x) ^ 2 + b * (2 + x) + c = a * (2 - x) ^ 2 + b * (2 - x) + c)
  (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c) : f 0.5 > f Real.pi := by
    specialize h 1
    ring_nf at h
    -- Since $f(2+x) = f(2-x)$, $\therefore$ The axis of symmetry of $f(x)$ is $x = 2$.
    have c1 : b / (2 * a) = -2 := by field_simp; linarith
    -- Transform the original equation to a * (x + b / (2 * a))^2 + (4 * a * c - b^2) / (4 * a).
    have c2 : f = fun x => a * (x + b / (2 * a))^2 + (4 * a * c - b^2) / (4 * a) := by
      simp [hf]
      ext x
      field_simp
      nlinarith
    simp [c1] at c2
    -- Simplifying the inequality $f(0.5) > f(\pi)$.
    simp [c2]
    rw [mul_lt_mul_left ha, sq_lt_sq]
    ring_nf
    simp [neg_div]
    rw [abs_eq_self.2 (by linarith [Real.pi_gt_three]), abs_eq_self.2 (by linarith)]
    simp [Real.pi_lt_315]
    calc
      _ < 3.15 := Real.pi_lt_315
      _ < _    := by
        rw [show (3 : ℝ) / 2 = 1.5 by norm_num]
        norm_num
