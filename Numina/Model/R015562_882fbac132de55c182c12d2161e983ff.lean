import Mathlib

theorem algebra_10402 (a b c d : ℤ) (h1 : 0 < a) (h2 : a < b) (h3 : b < c) (h4 : c < d)
    (h5 : Even a) (h6 : Even b) (h7 : Even c) (h8 : Even d) (h9 : 0 < d - a) (h10 : d - a = 90)
    (h11 : ∃ d₁, b = a + d₁ ∧ c = b + d₁) (h12 : ∃ r, c = b * r ∧ d = c * r) :
    a + b + c + d = 194 := by
  rcases h11 with ⟨d₁, h111, h112⟩
  rcases h12 with ⟨r, h121, h122⟩
  have h13 : d = a + 90 := by
    linarith
  have eq1 : c = a + 2 * d₁ := by
    nlinarith [h111, h112]
  have eq2 : a + 2 * d₁ = b * r := by
    nlinarith [eq1, h121, h111]
  have eq3 : b = a + d₁ := by
    linarith [h111]
  have eq4 : a + 90 = c * r := by
    nlinarith [h13, h122, eq1]
  rw [show c = a + 2 * d₁ by nlinarith [eq1]] at eq4
  have eq5 : a + 2 * d₁ = (a + d₁) * r := by
    rw [eq3] at eq2
    linarith
  have eq6 : a + 90 = (a + 2 * d₁) * r := by
    linarith
  have eq7 : r > 0 := by 
    nlinarith [show 0 < a by linarith, show 0 < a + 2 * d₁ by nlinarith]
  have eq8 : r ≤ 9 := by
    nlinarith [sq_nonneg ((a + 2 * d₁) * r - (a + 90)), sq_nonneg (a + 2 * d₁ - (a + 90) / 2), sq_nonneg ((a + 2 * d₁) * r - (a + 90)), sq_nonneg (a * r - (a + 2 * d₁) * r / 2), sq_nonneg (a * r * (a * r)), h1, sq_nonneg (d₁ * r - 45)]
  interval_cases r <;> try { 
    omega 
  }