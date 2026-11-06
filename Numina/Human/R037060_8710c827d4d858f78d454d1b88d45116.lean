import Mathlib

/- Let's determine the real roots of the following equation:


$$

2 x^{4}+4 x^{3}+3 x^{2}+x-1=0

$$
 -/
theorem algebra_235967 (x : ℝ) : 2*x^4+4*x^3+3*x^2+x-1=0 ↔ x=-1/2+Real.sqrt 3/2 ∨ x=-1/2-Real.sqrt 3/2 := by
  -- do the substitution with z where z = x + 1/2
  set z := x + 1/2 with hz
  have hx : x = z - 1/2 := by linarith
  rw [hx]
  -- this converts equation to z^4 = 9/16, from which result is easy to prove
  calc
    2 * (z - 1 / 2) ^ 4 + 4 * (z - 1 / 2) ^ 3 + 3 * (z - 1 / 2) ^ 2 + (z - 1 / 2) - 1 = 0 ↔ 2 * (z^4 - 9 / 16) = 0 := by
      constructor
      repeat
        rintro h
        rw [← h]
        ring
    _ ↔ z^4 = 9/16 := by constructor <;> (rintro h; linarith)
    _ ↔ z^4 = (√3/2)^4 := by
      rw [div_pow, (show √3^4 = (√3^2)^2 by ring)]
      simp; norm_num
    _ ↔ z = √3/2 ∨ z = -(√3/2) ∧ Even 4 := by exact pow_eq_pow_iff_of_ne_zero (by norm_num)
    _ ↔ z = √3/2 ∨ z = -(√3/2) := by
      have : Even 4 := by use 2
      simp [this]
    _ ↔ _ := by
      have : z = √3 / 2 ↔ z - 1 / 2 = -1 / 2 + √3 / 2 := by constructor <;> (rintro h; linarith)
      rw [this]
      have : z = -(√3 / 2) ↔ z - 1 / 2 = -1 / 2 - √3 / 2 := by constructor <;> (rintro h; linarith)
      rw [this]