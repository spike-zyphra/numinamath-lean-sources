import Mathlib

theorem algebra_312811 (f : ℝ → ℝ) (b : ℝ) (hf : f = fun x => x^3 - 6 * b * x + 3 * b)
    (hmin : ∃ x ∈ Set.Ioo 0 1, deriv f x = 0) :
    b ∈ Set.Ioo 0 (1 / 2) := by
  rcases hmin with ⟨x, hx, hfx⟩
  rw [hf] at hfx
  have hderiv : deriv (fun (x : ℝ) => x ^ 3 - 6 * b * x + 3 * b) x = 3 * x ^ 2 - 6 * b := by
    simp [deriv_pow, deriv_const, deriv_sub, deriv_add, deriv_mul, mul_comm]
    all_goals field_simp
    <;> ring_nf <;> field_simp <;> ring
  rw [hderiv] at hfx
  have h1 : 3 * x^2 - 6 * b = 0 := by
    simpa using hfx
  have h2 : x^2 = 2 * b := by
    nlinarith
  rcases hx with ⟨hx1, hx2⟩
  have hx3 : x ^ 2 > 0 := by nlinarith
  have hx4 : x ^ 2 < 1 := by nlinarith [sq_nonneg (x - 1)]
  have hb1 : 0 < b := by 
    nlinarith [h2, hx3]
  have hb2 : b < 1 / 2 := by
    nlinarith [h2, hx4]
  constructor
  · exact hb1
  · exact hb2