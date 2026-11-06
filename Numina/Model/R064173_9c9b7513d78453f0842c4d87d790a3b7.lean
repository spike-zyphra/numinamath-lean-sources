import Mathlib

theorem algebra_269346
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 / ((a - b) * (a - c)) + 1 / ((b - c) * (b - a)) + 1 / ((c - a) * (c - b)) = 0 ∧
    a / ((a - b) * (a - c)) + b / ((b - c) * (b - a)) + c / ((c - a) * (c - b)) = 0 ∧
    a ^ 2 / ((a - b) * (a - c)) + b ^ 2 / ((b - c) * (b - a)) + c ^ 2 / ((c - a) * (c - b)) = 1 := by
  have h1 : a ≠ b := habc.1
  have h2 : a ≠ c := habc.2.1
  have h3 : b ≠ c := habc.2.2
  constructor
  · -- Proof of 1/(a-b)(a-c)+1/(b-c)(b-a)+1/(c-a)(c-b)=0
    have h4 : a - b ≠ 0 := sub_ne_zero_of_ne h1
    have h5 : a - c ≠ 0 := sub_ne_zero_of_ne h2
    have h6 : b - c ≠ 0 := sub_ne_zero_of_ne h3
    have h7 : b - a ≠ 0 := by
      intro h
      apply h1
      linarith
    have h8 : c - a ≠ 0 := by
      intro h
      apply h2
      linarith
    have h9 : c - b ≠ 0 := by
      intro h
      apply h3
      linarith
    field_simp [h4, h5, h6, h7, h8, h9]
    ring
  constructor
  · -- Proof of a/(a-b)(a-c)+b/(b-c)(b-a)+c/(c-a)(c-b)=0
    have h4 : a - b ≠ 0 := sub_ne_zero_of_ne h1
    have h5 : a - c ≠ 0 := sub_ne_zero_of_ne h2
    have h6 : b - c ≠ 0 := sub_ne_zero_of_ne h3
    have h7 : b - a ≠ 0 := by
      intro h
      apply h1
      linarith
    have h8 : c - a ≠ 0 := by
      intro h
      apply h2
      linarith
    have h9 : c - b ≠ 0 := by
      intro h
      apply h3
      linarith
    field_simp [h4, h5, h6, h7, h8, h9]
    ring
  · -- Proof of a^2/(a-b)(a-c)+b^2/(b-c)(b-a)+c^2/(c-a)(c-b)=1
    have h4 : a - b ≠ 0 := sub_ne_zero_of_ne h1
    have h5 : a - c ≠ 0 := sub_ne_zero_of_ne h2
    have h6 : b - c ≠ 0 := sub_ne_zero_of_ne h3
    have h7 : b - a ≠ 0 := by
      intro h
      apply h1
      linarith
    have h8 : c - a ≠ 0 := by
      intro h
      apply h2
      linarith
    have h9 : c - b ≠ 0 := by
      intro h
      apply h3
      linarith
    field_simp [h4, h5, h6, h7, h8, h9]
    ring