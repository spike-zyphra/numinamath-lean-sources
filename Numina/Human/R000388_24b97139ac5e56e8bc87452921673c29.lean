import Mathlib

open Real Set
open scoped BigOperators

/-Given that the inequality $(ax-20) \lg \frac{2a}{x} \leqslant 0$ holds true for any positive real number $x$, determine the range of values for the real number $a$.-/
theorem algebra_9359 {a : ℝ} (ha : 0 < a) :
  (∀ x > 0, (a * x - 20) * log (2 * a / x) ≤ 0) ↔ a = sqrt 10 := by
    constructor <;> intro h
    · -- The inequality $(ax-20) \lg \frac{2a}{x} \leqslant 0$ holds for any postivite real number $x$,
      -- so we let $x = 2 \sqrt{10}$.
      simp [mul_nonpos_iff] at h
      specialize h (2 * √10) (by simp)
      -- There are two cases : $ \begin{cases} ax-20 \leqslant 0 \\ \lg \frac{2a}{x} \geqslant 0 \\ x > 0 \end{cases}$ or
      -- $ \begin{cases} ax-20 \geqslant 0 \\ \lg \frac{2a}{x} \leqslant 0 \\ x > 0 \end{cases}$.
      rcases h with h | h
      · -- $ \begin{cases} ax-20 \geqslant 0 \\ \lg \frac{2a}{x} \leqslant 0 \\ x > 0 \end{cases}$
        apply eq_of_le_of_le
        · have := (Real.log_nonpos_iff (by simp [ha])).1 h.2
          simp at this
          rw [div_le_one (by simp)] at this
          linarith
        · have : 20 / (2 * √10) = √10 := by
            rw [div_eq_iff (by simp)]
            ring_nf; simp; ring
          rw [←div_le_iff₀ (by simp), this] at h
          exact h.1
      · -- $ \begin{cases} ax-20 \leqslant 0 \\ \lg \frac{2a}{x} \geqslant 0 \\ x > 0 \end{cases}$
        apply eq_of_le_of_le
        · have : 20 / (2 * √10) = √10 := by
            rw [div_eq_iff (by simp)]
            ring_nf; simp; ring
          rw [←le_div_iff₀ (by simp), this] at h
          exact h.1
        · have := (Real.log_nonneg_iff (by simp [ha])).1 h.2
          rw [one_le_div (by simp)] at this
          linarith
    · -- Verify that when $a = 2\sqrt {10}$, the inequality
      -- $(ax-20) \lg \frac{2a}{x} \leqslant 0$ holds true for any positive real number $x$
      simp [h]
      intro x xpos
      by_cases hx : x ≤ 2*√10
      · have h1 : √10 * x - 20 ≤ 0 := by
          calc _ ≤ √10 * (2 * √10) - 20 := by simp [hx]
               _ = 0 := by ring_nf; simp; ring
        have h2 : 0 ≤ log (2 * √10 / x) := by
          apply (Real.log_nonneg_iff (by simp [xpos])).2
          rwa [one_le_div xpos]
        exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      · push_neg at hx
        have h1 : 0 < √10 * x - 20 := by
          calc _ ≤  √10 * (2 * √10) - 20 := by  ring_nf; simp; linarith
               _ <  √10 * x - 20 := by simp [hx]
        have h2 : log (2 * √10 / x) < 0 := by
          apply (Real.log_neg_iff (by simp [xpos])).2
          rwa [div_lt_one xpos]
        exact le_of_lt (mul_neg_of_pos_of_neg h1 h2)
