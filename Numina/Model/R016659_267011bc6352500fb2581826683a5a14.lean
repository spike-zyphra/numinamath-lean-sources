import Mathlib

theorem algebra_94634 {x y z a b c : ℝ} (hxy : x * y = a) (hxz : x * z = b) (hyz : y * z = c)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    x ^ 2 + y ^ 2 + z ^ 2 = ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) / (a * b * c) := by

  have h1 : x ^ 2 = (a * b) / c := by
    have h2 : x ^ 2 = (x * y) * (x * z) / (y * z) := by
      field_simp [(show y * z ≠ 0 by
        intro h'
        apply hc
        linarith)]
      <;> ring
    rw [h2, hxy, hxz, hyz]

  have h2 : y ^ 2 = (a * c) / b := by
    have h3 : y ^ 2 = (x * y) * (y * z) / (x * z) := by
      field_simp [(show x * z ≠ 0 by
        intro h'
        apply hb
        linarith)]
      <;> ring
    rw [h3, hxy, hyz, hxz]

  have h3 : z ^ 2 = (b * c) / a := by
    have h4 : z ^ 2 = (x * z) * (y * z) / (x * y) := by
      field_simp [(show x * y ≠ 0 by
        intro h'
        apply ha
        linarith)]
      <;> ring
    rw [h4, hxz, hyz, hxy]

  have h4 : x ^ 2 + y ^ 2 + z ^ 2 = (a * b) / c + (a * c) / b + (b * c) / a := by
    rw [h1, h2, h3]

  have h5 : (a * b) / c + (a * c) / b + (b * c) / a = ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) / (a * b * c) := by
    field_simp [ha, hb, hc, show a * b * c ≠ 0 by
          apply mul_ne_zero
          apply mul_ne_zero
          exact ha
          exact hb
          exact hc]
    <;> ring

  rw [h4]
  exact h5