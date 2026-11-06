import Mathlib

theorem algebra_174107 {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h : (a * b, b * c, c * a) = (p * a, p * b, p * c)) :
    p = (a * b * c) ^ 21 := by
  rcases hne with ⟨ha1, ha2, hb1⟩
  have eq1 := congrArg (λ x => x.1) h
  have eq2 := congrArg (λ x => x.2.1) h
  have eq3 := congrArg (λ x => x.2.2) h
  simp at eq1 eq2 eq3
  have h1 : b = p := by
    apply (mul_left_inj' (ne_of_gt ha)).mp 
    linarith
  have h2 : c = p := by
    apply (mul_left_inj' (ne_of_gt hb)).mp 
    linarith
  have h3 : a = p := by
    apply (mul_left_inj' (ne_of_gt hc)).mp 
    linarith
  have h4 : a = b := by linarith [h1, h3]
  contradiction