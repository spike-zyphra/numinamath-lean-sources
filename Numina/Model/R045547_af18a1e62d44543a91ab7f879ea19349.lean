import Mathlib

theorem algebra_245965 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * b * c / (a * b + b * c + a * c) = x) :
    1 / a + 1 / b + 1 / c = 1 / x := by
  have h1 : 1 / a + 1 / b + 1 / c = (a * b + b * c + a * c) / (a * b * c) := by
    field_simp [ha, hb, hc]
    <;> ring
  have hx_eq : x = a * b * c / (a * b + b * c + a * c) := by
    linarith [h]
  have h_abc_ne_zero : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  by_cases h2 : a * b + b * c + a * c = 0
  · -- If $a*b + b*c + a*c = 0$, then $X = 0$.
    have hx0 : x = 0 := by
      rw [hx_eq]
      rw [h2]
      norm_num
    rw [h1, hx0]
    norm_num [h2, h_abc_ne_zero]
    all_goals linarith
  · -- If $a*b + b*c + a*c \neq 0$.
    have h2' : 1 / x = (a * b + b * c + a * c) / (a * b * c) := by
      rw [hx_eq]
      have h3 : a * b + b * c + a * c ≠ 0 := by
        intro h'
        apply h2
        linarith
      have h4 : a * b * c ≠ 0 := by
        exact h_abc_ne_zero
      field_simp [h3, h4]
      <;> ring_nf <;> field_simp [h3, h4]
      <;> ring
      all_goals linarith
    rw [h1, h2']
    all_goals linarith
    all_goals try { tauto }
    all_goals try { nlinarith }
    all_goals try { tauto }
    all_goals try { tauto }
    all_goals try { tauto }
    all_goals try { tauto }