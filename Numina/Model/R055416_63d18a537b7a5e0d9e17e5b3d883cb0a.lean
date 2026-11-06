import Mathlib

theorem algebra_313594 {x : ℝ} (hx : x > 0) (h : x^2 + 1/x^2 = 7) :
    ∃ n, x^5 + 1/x^5 = n ∧ n = 123 := by
  have h1 : x + 1 / x = 3 := by
    have h2 : (x + 1 / x) ^ 2 = 9 := by
      calc 
        (x + 1 / x) ^ 2 = x^2 + 1 / x^2 + 2 := by 
          field_simp
          <;> ring
        _ = 7 + 2 := by rw [h]
        _ = 9 := by norm_num
    have h3 : x + 1 / x > 0 := by 
      positivity
    have h4 : x + 1 / x = 3 := by nlinarith
    exact h4
  have h3 : x^3 + 1 / x^3 = 18 := by
    calc
      x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
        field_simp
        <;> ring
      _ = (3) ^ 3 - 3 * (3) := by rw [h1]
      _ = 18 := by norm_num
  have h4 : x^4 + 1 / x^4 = 47 := by
    calc
      x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
        field_simp
        <;> ring
      _ = (7) ^ 2 - 2 := by rw [h]
      _ = 47 := by norm_num
  have h5 : x^5 + 1 / x^5 = 123 := by
    calc 
      x^5 + 1 / x^5 = (x + 1 / x) * (x^4 + 1 / x^4) - (x^3 + 1 / x^3) := by
        field_simp
        <;> ring
      _ = 3 * (47) - (18) := by rw [h1, h4, h3]
      _ = 123 := by norm_num
  exact ⟨123, by linarith [h5], rfl⟩