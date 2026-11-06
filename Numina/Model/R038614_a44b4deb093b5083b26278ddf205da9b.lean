import Mathlib

theorem algebra_15346 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) /
    ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) = (a + b) * (a + c) * (b + c) := by

  have h1 : a - b ≠ 0 := by
    intro h2
    apply ha
    linarith

  have h2 : b - c ≠ 0 := by
    intro h3
    apply hb
    linarith

  have h3 : c - a ≠ 0 := by
    intro h4
    apply hc
    have h5 : a = c := by linarith
    contradiction

  have h4 : (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 ≠ 0 := by
    have h5 : (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 = 3 * ((a - b) * (b - c) * (c - a)) := by
      ring_nf
    rw [h5]
    have h6 : (a - b) * (b - c) * (c - a) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      · exact h1
      · exact h2
      · exact h3
    intro h
    have h7 : (a - b) * (b - c) * (c - a) = 0 := by
      linarith
    contradiction

  have h6 : (a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3 = 3 * ((a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) * (c ^ 2 - a ^ 2)) := by
    ring_nf

  have h7 : (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 = 3 * ((a - b) * (b - c) * (c - a)) := by
    ring_nf

  rw [h6, h7]

  have h8 : (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) * (c ^ 2 - a ^ 2) = (a + b) * (a + c) * (b + c) * ((a - b) * (b - c) * (c - a)) := by
    ring_nf

  rw [h8]

  field_simp [h1, h2, h3, show (a - b) * (b - c) * (c - a) ≠ 0 by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h1
    exact h2
    exact h3
  ]
  <;> ring