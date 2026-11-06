import Mathlib

theorem algebra_298144 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y + x + y = 23) (h2 : x ^ 2 * y + x * y ^ 2 = 120) :
    x ^ 2 + y ^ 2 = 34 := by
  have h3 : x ≤ 11 := by
    by_contra h
    push_neg at h
    have h4 : y ≤ 1 := by
      nlinarith [h1, h]
    have h5 : y = 0 ∨ y = 1 := by
      interval_cases y <;> omega
    cases h5 with
    | inl h6 =>
      nlinarith [h1, h6, show 0 < x by linarith, show 0 < y by linarith]
    | inr h7 =>
      nlinarith [h1, h7, show 0 < x by linarith, show 0 < y by linarith]
  have h4 : y ≤ 11 := by
    by_contra h
    push_neg at h
    have h5 : x ≤ 1 := by
      nlinarith [h1, h]
    have h6 : x = 0 ∨ x = 1 := by
      interval_cases x <;> omega
    cases h6 with
    | inl h7 =>
      nlinarith [h1, h7, show 0 < x by linarith, show 0 < y by linarith]
    | inr h8 =>
      nlinarith [h1, h8, show 0 < x by linarith, show 0 < y by linarith]
  interval_cases x <;> interval_cases y
    <;> omega  -- substituting the possible x and y, check the equations