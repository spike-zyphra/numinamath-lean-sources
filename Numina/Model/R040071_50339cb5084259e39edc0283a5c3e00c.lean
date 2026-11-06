import Mathlib

theorem inequalities_605291 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    1 / (a ^ 5 + b ^ 5 + c ^ 2) + 1 / (b ^ 5 + c ^ 5 + a ^ 2) + 1 / (c ^ 5 + a ^ 5 + b ^ 2) ≤ 1 := by

  have lemma₀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x ^ 5 + y ^ 5 ≥ x * y * (x ^ 3 + y ^ 3) := by
    nlinarith [sq_nonneg (x - y), show 0 ≤ (x ^ 2 + y ^ 2) * (x + y) by positivity]

  calc
    1 / (a ^ 5 + b ^ 5 + c ^ 2) + 1 / (b ^ 5 + c ^ 5 + a ^ 2) + 1 / (c ^ 5 + a ^ 5 + b ^ 2)
    _ ≤ 1 / (a * b * (a ^ 3 + b ^ 3 + c ^ 3)) + 1 / (b * c * (b ^ 3 + c ^ 3 + a ^ 3)) + 1 / (c * a * (c ^ 3 + a ^ 3 + b ^ 3)) := by
      apply add_le_add
      apply add_le_add
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show c ^ 3 = c * c ^ 2 by ring, <-mul_assoc, habc, one_mul]
      apply add_le_add
      exact lemma₀ a b ha hb
      rfl
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show a ^ 3 = a * a ^ 2 by ring, <-mul_assoc, show b * c * a = a * b * c by ring, habc, one_mul]
      apply add_le_add
      exact lemma₀ b c hb hc
      rfl
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show b ^ 3 = b * b ^ 2 by ring, <-mul_assoc, show c * a * b = a * b * c by ring, habc, one_mul]
      apply add_le_add
      exact lemma₀ c a hc ha
      rfl
    _ = 1 / (a ^ 3 + b ^ 3 + c ^ 3) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
      field_simp
      ring
    _ ≤ 1 := by
      have h1 : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) = (a + b + c) / (a * b * c) := by
        field_simp
        ring
      rw [h1]
      have h2 : a * b * c = 1 := habc
      have h3 : 1 / (a ^ 3 + b ^ 3 + c ^ 3) * ((a + b + c) / (a * b * c)) = (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by
          field_simp [h2]
          <;> nlinarith
      rw [h3]
      have h4 : a + b + c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a * b * c - 1), habc]
      have h5 : (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        nlinarith
      linarith [h5]