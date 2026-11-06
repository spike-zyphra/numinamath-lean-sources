import Mathlib

theorem number_theory_283900 {x y z: ℤ} (lx: 0 < x) (l1: x ≤ y) (l2: y ≤ z) (l3: z ≤ x + 6)
  (h: x * y * z = 2808): x = 12 := by
  have h1 : x ≤ z := by linarith [l1, l2]
  have h2 : z ≤ x + 6 := l3
  have h3 : y ≤ x + 6 := by linarith [l2, l3]
  have h4 : x ≥ 1 := by linarith
  -- Upper bound for x
  have h5 : x ≤ 18 := by
    by_contra h5
    push_neg at h5
    have h6 : y ≥ 19 := by linarith [l1, h5]
    have h7 : z ≥ 19 := by linarith [l2, h6]
    have h8 : x * y * z ≥ 19 * 19 * 19 := by
      have h9 : x ≥ 19 := by linarith [h5]
      have h10 : y ≥ 19 := by linarith [h6]
      have h11 : z ≥ 19 := by linarith [h7]
      have h12 : x * y ≥ 19 * 19 := by
        nlinarith
      nlinarith
    nlinarith -- contradiction
  have h6 : y ≤ 24 := by
    nlinarith [h5]
  have h7 : z ≤ 24 := by
    nlinarith [h5, h3]
  interval_cases x <;> interval_cases y
  <;> omega