import Mathlib
theorem algebra_604918 : (∀ a b k : ℝ, a > 0 → b > 0 → a < b → k > 0 → a / b < (a + k) / (b + k)) ∧ (∑ i in Finset.range (50), (1 + 3 * (↑i : ℝ)) / (100 + ↑i) > 25):= by
  constructor
  · -- General Inequality
    intro a b k ha hb h1 hk
    have h4 : a * (b + k) < b * (a + k):= by
      have hk2 : a * k < b * k:= by
        apply mul_lt_mul_of_pos_right
        all_goals linarith
      have h5 : a * (b + k) = a * b + a * k := by ring
      have h6 : b * (a + k) = b * a + b * k := by ring
      rw [h5, h6]
      nlinarith
    have h3 : a / b < (a + k) / (b + k):= by
      have hb2 : b > 0 := hb
      have hk2 : b + k > 0 := by linarith
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h3
  · -- Part 2
    norm_num [Finset.sum_range_succ]
    <;> try { norm_num }
    <;> try { linarith }
    <;> norm_num
    <;> try { linarith }
    <;> norm_num
    <;> try { linarith }
    <;> norm_num