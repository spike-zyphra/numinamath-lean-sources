import Mathlib

theorem algebra_95388 {m n r t : ℝ} (hmn : m / n = 4 / 3) (hrr : r / t = 9 / 14) :
    (3 * m * r - n * t) / (4 * n * t - 7 * m * r) = -11 / 14 := by
  have hn : n ≠ 0 := by 
    by_contra h
    rw [h] at hmn 
    field_simp at hmn 
  have ht : t ≠ 0 := by 
    by_contra h
    rw [h] at hrr 
    field_simp at hrr 
  -- From $\frac{m}{n} = \frac{4}{3}$, we have $m = \frac{4}{3}n$.
  have h1 : m = 4 / 3 * n := by 
    have hmn' : m / n = 4 / 3 := hmn 
    field_simp [hn] at hmn' 
    linarith
  -- From $\frac{r}{t} = \frac{9}{14}$, we have $r = \frac{9}{14}t$.
  have h2 : r = 9 / 14 * t := by
    have hrr' : r / t = 9 / 14 := hrr 
    field_simp [ht] at hrr' 
    linarith
  have h3 : 3 * m * r - n * t = 11 / 7 * (n * t) := by 
    rw [h1, h2]
    linarith
  have h4 : 4 * n * t - 7 * m * r = -2 * (n * t) := by
    rw [h1, h2]
    linarith 
  have h5 : (3 * m * r - n * t) / (4 * n * t - 7 * m * r) = -11 / 14 := by
    rw [h3, h4]
    have ht1 : n * t ≠ 0 := by 
      apply mul_ne_zero 
      exact hn 
      exact ht 
    field_simp [ht1] 
    <;> ring 
  exact h5