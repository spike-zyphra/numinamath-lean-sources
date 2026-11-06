import Mathlib

theorem algebra_305548 {k : ℝ} (h : ∃ a b, ∀ x y, (100*x^2-k*x*y+49*y^2) = (a*x+b*y)^2) :
    k = 140 ∨ k = -140 := by
  rcases h with ⟨a,b,h_eq⟩
  have h1 := h_eq 1 0
  have h2 := h_eq 0 1
  have h3 := h_eq 1 1
  have h4 := h_eq 1 (-1)
  ring_nf at h1 h2 h3 h4
  have ha : a^2 = 100 := by
    nlinarith
  have hb : b^2 = 49 := by
    nlinarith
  have hk1 : 2 * a * b = -k := by
    nlinarith [h1, h2, h3]
  have ha1 : a = 10 ∨ a = -10 := by
    have h10 : a^2 - 100 = 0 := by linarith
    have h11 : (a - 10) * (a + 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with ha10 ha11
    · left
      linarith
    · right
      linarith
  have hb1 : b = 7 ∨ b = -7 := by
    have h7 : b^2 - 49 = 0 := by linarith
    have h8 : (b - 7) * (b + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with hb1 hb2
    · left
      linarith
    · right
      linarith
  cases ha1 with
  | inl ha10 =>
    cases hb1 with
    | inl hb7 =>
      have hk : k = -140 := by
        nlinarith [show 2 * a * b = -k from by linarith [hk1]]
      right
      linarith
    | inr hb7 =>
      have hk : k = 140 := by
        nlinarith [show 2 * a * b = -k from by linarith [hk1]]
      left
      linarith
  | inr ha11 =>
    cases hb1 with
    | inl hb7 =>
      have hk : k = 140 := by
        nlinarith [show 2 * a * b = -k from by linarith [hk1]]
      left
      linarith
    | inr hb7 =>
      have hk : k = -140 := by
        nlinarith [show 2 * a * b = -k from by linarith [hk1]]
      right
      linarith