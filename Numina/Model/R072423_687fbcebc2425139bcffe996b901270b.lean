import Mathlib

theorem algebra_270600 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : ∃ x, x^2 + 2 * a * x + b^2 = 0 ∧
    x^2 + 2 * c * x - b^2 = 0) :
    a^2 = b^2 + c^2 := by 
  rcases h''' with ⟨x, hx1, hx2⟩
  have eq1 : 2 * a * x - 2 * c * x + 2 * b^2 = 0 := by linarith
  have eq2 : x * (a - c) + b^2 = 0 := by
    linarith
  have h_eq3 : x^2 + 2 * a * x + b^2 = 0 := hx1
  have h_eq4 : x * (x + a + c) = 0 := by
    rw [show b^2 = -x * (a - c) by linarith] at h_eq3
    ring_nf at h_eq3 ⊢
    linarith [sq_nonneg (x), sq_nonneg (a - c), sq_nonneg (x + a + c)]
  cases' (mul_eq_zero.mp h_eq4) with h_eq5 h_eq6
  · -- If x = 0, then from eq2: $x * (a - c) + b^2 = 0$ would give $b^2 = 0$, which is a contradiction with hb > 0
    have h0 : x = 0 := by linarith
    rw [h0] at eq2
    nlinarith [hb, sq_nonneg (b)]
  · -- Therefore, we must have x + a + c = 0, which gives x = -a - c
    have h_x : x = -a - c := by linarith
    rw [h_x] at eq2
    nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]