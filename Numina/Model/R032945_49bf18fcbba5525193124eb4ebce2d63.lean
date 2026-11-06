import Mathlib

theorem algebra_211418 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hord : a * b < a * c ∧ a * b < a * d ∧ a * c < a * d ∧ b * c < b * d ∧ c * d < a * b)
    (hdiff : ∃ x, a * b - x = a * c ∧ a * c - x = a * d ∧ a * d - x = b * c ∧ b * c - x = b * d ∧ c * d - x = a * b) :
    False := by

  rcases hdiff with ⟨x, h1, h2, h3, h4, h5⟩
  have eq1 : a * b + a * d = 2 * a * c := by
    nlinarith
  have eq2 : b + d = 2 * c := by
    have h : 0 < a := ha
    have eq11 : a * b + a * d = 2 * a * c := by
      nlinarith
    have : a * (b + d) = 2 * a * c := by
      linarith
    have : b + d = 2 * c := by
      apply (mul_left_inj' (ne_of_gt ha)).mp
      linarith
    assumption

  nlinarith [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2, ha, hb, hc, hd, hord.1, hord.2.1, hord.2.2.1, hord.2.2.2.1, hord.2.2.2.2]