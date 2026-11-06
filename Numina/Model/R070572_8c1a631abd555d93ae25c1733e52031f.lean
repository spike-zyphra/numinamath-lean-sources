import Mathlib

theorem algebra_165443 {a b c x : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    a^2 * (x - b) * (x - c) / ((a - b) * (a - c)) +
    b^2 * (x - c) * (x - a) / ((b - c) * (b - a)) +
    c^2 * (x - a) * (x - b) / ((c - a) * (c - b)) = x^2 := by
  have h1 : a - b ≠ 0 := sub_ne_zero_of_ne ha
  have h2 : b - c ≠ 0 := sub_ne_zero_of_ne hb
  have h3 : a - c ≠ 0 := sub_ne_zero_of_ne hc
  have h4 : b - a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h5 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith
  have h6 : c - b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [(show (a - b : ℝ) ≠ 0 by exact h1), 
            (show (a - c : ℝ) ≠ 0 by exact h3), 
            (show (b - c : ℝ) ≠ 0 by exact h2), 
            (show (b - a : ℝ) ≠ 0 by exact h4), 
            (show (c - a : ℝ) ≠ 0 by exact h5), 
            (show (c - b : ℝ) ≠ 0 by exact h6)]
  <;> ring_nf <;> field_simp [(show (a - b : ℝ) ≠ 0 by exact h1), 
                            (show (a - c : ℝ) ≠ 0 by exact h3), 
                            (show (b - c : ℝ) ≠ 0 by exact h2), 
                            (show (b - a : ℝ) ≠ 0 by exact h4), 
                            (show (c - a : ℝ) ≠ 0 by exact h5), 
                            (show (c - b : ℝ) ≠ 0 by exact h6)]
  <;> nlinarith