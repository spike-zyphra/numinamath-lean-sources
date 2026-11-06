import Mathlib

theorem algebra_183209 {a b c d : ℤ} (p : ℤ → ℤ) (hp : p = fun x => a * x^3 + b * x^2 + c * x + d)
    (h1 : p 1 = 2015) (h2 : p 2 = 2017) :
    ¬∃ x : ℤ, p x = 2016 := by 
  simp [hp] at h1 h2 
  rintro ⟨x, hx⟩
  simp [hp] at hx
  have eq1 : a + b + c + d = 2015 := by linarith 
  have eq2 : 8 * a + 4 * b + 2 * c + d = 2017 := by linarith 
  have eq3 : 7 * a + 3 * b + c = 2 := by linarith 
  have eq4 : a * x ^ 3 + b * x ^ 2 + c * x + d = 2016 := by linarith 
  have eq5 : a * x ^ 3 + b * x ^ 2 + c * x + d - (a + b + c + d) = 1 := by linarith 
  have eq6 : a * (x ^ 3 - 1) + b * (x ^ 2 - 1) + c * (x - 1) = 1 := by 
    nlinarith 
  have eq7 : (x - 1) * (a * (x^2 + x + 1) + b * (x + 1) + c) = 1 := by 
    nlinarith [eq6] 
  have h8 : x - 1 = 1 ∨ x - 1 = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one
    exact eq7 
  cases h8 with
  | inl h8 =>
    have h9 : x = 2 := by linarith 
    rw [h9] at eq4
    omega 
  | inr h8 =>
    have h9 : x = 0 := by linarith 
    rw [h9] at eq4 
    omega