import Mathlib

theorem algebra_210959 {a b c m n k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (h1 : 1 / a = m / (b + c)) (h2 : 1 / b = n /(a + c))
    (h3 : 1 / c = k / (a + b)) :
    k = (m + n + 2) / (m * n - 1) := by

  have eq1 : b + c = a * m := by
    have h1' : a ≠ 0 := by linarith
    have h11' : b + c ≠ 0 := by nlinarith
    field_simp [h1'] at h1 ⊢
    <;> nlinarith
  have eq2 : a + c = b * n := by
    have h2' : b ≠ 0 := by linarith
    have h22' : a + c ≠ 0 := by nlinarith
    field_simp [h2'] at h2 ⊢
    <;> nlinarith
  have eq3 : a + b = c * k := by
    have h3' : c ≠ 0 := by linarith
    have h33' : a + b ≠ 0 := by nlinarith
    field_simp [h3'] at h3 ⊢
    <;> nlinarith
  have eq4 : b = a * (m + 1) / (1 + n) := by
    have : 1 + n ≠ 0 := by nlinarith
    have eq5 : a + c = b * n := by linarith [eq2]
    have eq55 : b + c = a * m := by linarith [eq1]
    field_simp at eq5 eq55 ⊢
    <;> nlinarith [sq_nonneg (b - a * (m + 1) / (1 + n)), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hn]
  have eq5 : c = a * (m * n - 1) / (1 + n) := by
    have eq1' : b + c = a * m := by linarith [eq1]
    have eq4' : b = a * (m + 1) / (1 + n) := by linarith [eq4]
    rw [eq4'] at eq1'
    have h77 : 1 + n ≠ 0 := by nlinarith
    field_simp at eq1' ⊢
    <;> nlinarith
  have eq6 : k = (m + n + 2) / (m * n - 1) := by
    have eq3' : a + b = c * k := by linarith [eq3]
    rw [show b = a * (m + 1) / (1 + n) by linarith [eq4]] at eq3'
    rw [show c = a * (m * n - 1) / (1 + n) by linarith [eq5]] at eq3'
    have h11' : m * n - 1 ≠ 0 := by
      by_contra h
      have h11 : m * n = 1 := by linarith
      have h55 : c = 0 := by
        rw [show c = a * (m * n - 1) / (1 + n) by linarith [eq5]]
        field_simp [h11]
        <;> nlinarith
      linarith
    have h1' : 1 + n > 0 := by linarith
    have ha' : a > 0 := by linarith
    have h55 : m * n - 1 ≠ 0 := h11'
    field_simp [h11', ha'] at eq3' ⊢
    <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hn, sq_pos_of_pos hk, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos hn hm]
  exact_mod_cast eq6