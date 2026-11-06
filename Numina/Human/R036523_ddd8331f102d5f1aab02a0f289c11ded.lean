import Mathlib

/- Given $x$ and $y$ are positive real numbers, satisfying $2x+y+6=xy$, find the minimum value of $xy$.-/
theorem algebra_9418 : IsLeast {z | ∃ x y : ℝ, z = x * y ∧ 0 < x ∧ 0 < y ∧
  2 * x + y + 6 = x * y } 18 := by
    -- Auxiliary lemma : for any positive number a b, 2 * √a * √b ≤ a + b .
    have aux {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 2 * √a * √b ≤ a + b := by
      rw [←pow_le_pow_iff_left (hn := show 2 ≠ 0 by linarith)] <;> try positivity
      rw [mul_pow, Real.sq_sqrt (by linarith), mul_pow, Real.sq_sqrt (by linarith)]
      linarith [two_mul_le_add_sq a b]

    constructor
    · -- when $x = 3$ and $y = 6$, $x * y$ reaches 18.
      use 3, 6
      split_ands <;> linarith
    · rintro z ⟨x, y, hz, xpos, ypos, c1⟩
      -- By applying the AM-GM inequality to the given condition, we have $xy = 2x + y + 6 \geq 2\sqrt{2xy} + 6$.
      have c2 : 2 * √(2 * x * y) + 6 ≤  x * y := by
        calc _ = 2 * √(2 * x) * √y + 6 := by rw [Real.sqrt_mul (by linarith)]; ring
             _ ≤ 2 * x + y + 6 := by
              simp only [Nat.ofNat_nonneg, add_le_add_iff_right]
              exact aux (by linarith) ypos
             _ = _ := c1
      -- Let $xy = t^2$, where $t = \sqrt{xy} > 0$,
      set t := √(x * y) with ht
      have ht2 : t^2 = x * y := by
        simp [ht, Real.sq_sqrt (show 0 ≤ x * y by positivity)]
      -- we get $t^2 - 2\sqrt{2}t - 6 \geq 0$.
      have c3 : 0 ≤ t^2 - 2 * √2 * t - 6 := by
        rw [←ht2, mul_assoc, Real.sqrt_mul (by simp), ←ht, ←mul_assoc] at c2
        linarith
      -- This simplifies to $(t - 3\sqrt{2})(t + \sqrt{2}) \geq 0$, which gives $t \leq -\sqrt{2}$ or $t \geq 3\sqrt{2}$.
      -- Considering $t > 0$, we have $t \geq 3\sqrt{2}$.
      have c4 : 3 * √2 ≤ t := by
        have c4 : 0 ≤ (t - 3 * √2) * (t + √2) := by
          simp [mul_add, sub_mul]
          ring_nf
          simp
          linarith
        have tpos : 0 < t := Real.sqrt_pos_of_pos (by positivity)
        have : 0 < t + √2 := tpos.trans (by simp)
        apply mul_nonneg_iff.1 at c4
        simp [this] at c4
        rcases c4 with hl | hr <;> linarith
      -- Therefore, $xy \geq 18$.
      have c5 : 18 ≤ x * y := by
        rw [ht] at c4
        have := (pow_le_pow_iff_left (by positivity) (by positivity) (show 2 ≠ 0 by simp)).2 c4
        simp [mul_pow, Real.sq_sqrt (show 0 ≤ x * y by positivity)] at this
        linarith

      linarith
