import Mathlib

/-- Three numbers $x, y,$ and $z$ are nonzero and satisfy the equations $x^{2}-y^{2}=y z$ and $y^{2}-z^{2}=x z$. Prove that $x^{2}-z^{2}=x y$.-/
theorem algebra_4017 (x y z : ℝ)(xn0 : x ≠ 0)(yn0 : y ≠ 0)(zn0 : z ≠ 0)
(h : x ^ 2 - y ^ 2 = y * z)(h' : y ^ 2 - z ^ 2 = x * z) :
x ^ 2 - z ^ 2 = x * y := by
  have t : ∀ u v : ℝ, u ≠ 0 → v ≠ 0 → u ^ 2 - v ^ 2 = v → v ^ 2 - 1 = u → u ^ 2 - 1 = u * v := by
    intro u v un0 _ h1 h1'
    rw [symm h1'] at h1; apply sub_eq_iff_eq_add.mp at h1; ring_nf at h1
    have q1 : v ^ 4 - 3 * v ^ 2 - v + 1 = 0 := by linarith
    have : (v + 1) * (v ^ 3 - v ^ 2 - 2 * v + 1) = v ^ 4 - 3 * v ^ 2 - v + 1 := by ring
    rw [symm this] at q1; simp at q1; cases q1 with
    | inl h => have : v = -1 := by linarith
               rw [this] at h1'; simp at h1'; symm at h1'; contradiction
    | inr h => have : v ^ 4 = 3 * v ^ 2 + v - 1 := by linarith
               rw [symm h1']; ring_nf; rw [this]; linarith
  have t1 : x / z ≠ 0 := by
    field_simp; push_neg; exact xn0
  have t2 : y / z ≠ 0 := by
    field_simp; push_neg; exact yn0
  -- transform `h` by dividing both sides by $z^2$.
  have t3 : (x / z) ^ 2 - (y / z) ^ 2 = y / z := by
    field_simp; rw [pow_two z]; rw [← mul_assoc]
    apply mul_eq_mul_right_iff.mpr; left; exact h
  -- transform `h‘` by dividing both sides by $z^2$.
  have t4 : (y / z) ^ 2 - 1 = x / z := by
    field_simp; rw [pow_two z]; rw [← mul_assoc]
    apply mul_eq_mul_right_iff.mpr; left; rw [← pow_two]; exact h'
  -- replace $(y / z) ^ 2$ by $x/z + 1$ in `t3` and simplify.
  have t5 : (x / z) ^ 2 - 1 = (x / z) * (y / z) := t (x / z) (y / z) t1 t2 t3 t4
  field_simp at t5; nth_rw 3 [pow_two] at t5
  apply mul_right_cancel₀ at t5; exact t5
  intro r; simp at r; contradiction
