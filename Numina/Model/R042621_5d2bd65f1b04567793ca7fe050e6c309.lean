import Mathlib

theorem algebra_289353 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : ∃ x, x^2 + 2 * a * x + b^2 = 0 ∧ x^2 + 2 * c * x - b^2 = 0)
    (h' : a + b > c) (h'' : a + c > b) (h''' : b + c > a) :
    a^2 + b^2 = c^2 ∨ b^2 + c^2 = a^2 ∨ c^2 + a^2 = b^2 := by
  rcases h with ⟨x, hx1, hx2⟩
  have eq1 : 2 * x^2 + 2 * x * (a + c) = 0 := by
    nlinarith
  have eq2 : 2 * (x) * (x + a + c) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq2) with eq3 eq4
  · -- Case where 2 * x = 0, so x = 0
    have hx0 : x = 0 := by linarith
    rw [hx0] at hx1
    nlinarith
  · -- Case where x + a + c = 0, so x = -a - c
    have hx0 : x = -a - c := by linarith
    rw [hx0] at hx1
    have h3 : b^2 + c^2 = a^2 := by nlinarith
    right
    left
    linarith