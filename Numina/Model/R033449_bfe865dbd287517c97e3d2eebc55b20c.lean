import Mathlib

open Real

/- If $a$, $b$, $c>0$, $\frac{1}{a}+\frac{2}{b}+\frac{3}{c}=1$, then the minimum value of $a+2b+3c$ is ___          ___. -/
theorem inequalities_9211 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 2 / b + 3 / c = 1) :
    a + 2 * b + 3 * c ≥ 36 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : (a + 2 * b + 3 * c) * (1 / a + 2 / b + 3 / c) ≥ 36 := by
    have h6 : 0 < a := ha
    have h7 : 0 < b := hb
    have h8 : 0 < c := hc
    have eq1 : (a + 2 * b + 3 * c) * (1 / a + 2 / b + 3 / c) =
      14 + 2 * (a / b + b / a) + 3 * (a / c + c / a) + 6 * (b / c + c / b) := by
      field_simp [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
      ring_nf
      <;> field_simp [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
      <;> ring
      all_goals try { tauto }
      <;> try { 
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc] 
      }
    have h5 : a / b + b / a ≥ 2 := by
      have h6 : a > 0 := ha
      have h7 : b > 0 := hb
      have h8 : a / b + b / a - 2 ≥ 0 := by
        have h9 : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by
          field_simp
          ring
        rw [h9]
        have h10 : (a - b) ^ 2 ≥ 0 := by
          exact sq_nonneg (a - b)
        have h11 : a * b > 0 := by positivity
        positivity
      nlinarith
    have h6 : a / c + c / a ≥ 2 := by
      have h7 : a > 0 := ha
      have h8 : c > 0 := hc
      have h9 : a / c + c / a - 2 ≥ 0 := by
        have h10 : a / c + c / a - 2 = (a - c) ^ 2 / (a * c) := by
          field_simp
          ring
        rw [h10]
        have h11 : (a - c) ^ 2 ≥ 0 := by
          exact sq_nonneg (a - c)
        have h12 : a * c > 0 := by positivity
        positivity
      nlinarith
    have h7 : b / c + c / b ≥ 2 := by
      have h8 : b > 0 := hb
      have h9 : c > 0 := hc
      have h10 : b / c + c / b - 2 ≥ 0 := by
        have h11 : b / c + c / b - 2 = (b - c) ^ 2 / (b * c) := by
          field_simp
          ring
        rw [h11]
        have h12 : (b - c) ^ 2 ≥ 0 := by
          exact sq_nonneg (b - c)
        have h13 : b * c > 0 := by positivity
        positivity
      nlinarith
    nlinarith [eq1, h5, h6, h7]
  have h5 : (a + 2 * b + 3 * c) * (1 / a + 2 / b + 3 / c) = (a + 2 * b + 3 * c) * 1 := by
    rw [h]
    all_goals try { tauto }
  rw [h5] at h4
  linarith