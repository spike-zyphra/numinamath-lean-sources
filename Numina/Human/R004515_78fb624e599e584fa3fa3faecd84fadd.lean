import Mathlib

/- Solve the following system of equations:


$$

\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=x+y+z=\frac{13}{3} ; \quad x y z=1

$$
 -/
theorem algebra_277589 {x y z : ℝ} :
    (1 / x + 1 / y + 1 / z = 13 / 3 ∧ x + y + z = 13 / 3 ∧ x * y * z = 1) ↔
    x = 1 ∧ y = 3 ∧ z = 1 / 3 ∨ x = 1 ∧ y = 1 / 3 ∧ z = 3 ∨
    x = 3 ∧ y = 1 / 3 ∧ z = 1 ∨ x = 3 ∧ y = 1 ∧ z = 1 / 3 ∨
    x = 1 / 3 ∧ y = 1 ∧ z = 3 ∨ x = 1 / 3 ∧ y = 3 ∧ z = 1 := by
  constructor <;> rintro h
  -- first we prove equations prove the values
  . obtain ⟨h1, h2, h3⟩ := h
    -- first of all x * y * z = 1 means none of x, y, z is 0, we prove a lemma to reuse
    have aux (a b c : ℝ) (h : a * b * c = 1) : a ≠ 0 := by
      by_contra ha
      rw [ha] at h
      simp at h
    -- next we prove each of x, y, z have values 1, 1/3, 3
    replace aux (x y z : ℝ) (h1 : 1/x + 1/y + 1/z = 13/3) (h2: x + y + z = 13/3) (h3 : x * y * z = 1) :
        x = 1 ∨ x = 3 ∨ x = 1/3 := by
      have hx := aux x y z h3
      have hy := aux y x z (by linarith)
      have hz := aux z x y (by linarith)
      -- multiply h1 by xyz to get xy + yz + zx
      replace h1 := congrArg (· * (x * y * z)) h1
      ring_nf at h1
      field_simp at h1
      rw [h3] at h1
      replace h1 : x * y + y * z + x * z = 13 / 3 := by linarith
      -- multiply h2 by x to get x^2 + yz + zx, also subtract h1 form them
      replace h2 := congrArg (· * x) h2
      ring_nf at h2
      replace h2 : x ^ 2 - y * z = x * (13 / 3) - 13 / 3 := by linarith
      -- writing yz = 1 / x and again multiplying x
      rw [show y * z = (x * y * z) / x by field_simp; ring, h3] at h2
      replace h2 := congrArg (· * x) h2
      ring_nf at h2
      field_simp at h2
      -- we get a expression which is (x-1) * (x - 3) * (x - 1/3), so we're done
      have : (x - 1) * (x - 3) * (x - 1/3) = 0 := by linarith
      simp at this
      repeat rw [sub_eq_zero] at this
      rw [or_assoc] at this
      simpa
    -- now for all those combinations, in some cases h1 is not satisfied, in some cases h3 is not satisfied, but in other cases goal is proved.
    have hx := aux x y z (by linarith) (by linarith) (by linarith)
    have hy := aux y x z (by linarith) (by linarith) (by linarith)
    have hz := aux z x y (by linarith) (by linarith) (by linarith)
    obtain rfl | rfl | rfl := hx <;> obtain rfl | rfl | rfl := hy <;> obtain rfl | rfl | rfl := hz
    all_goals norm_num at h3
    all_goals norm_num at h1
    all_goals simp
  -- for other way, for each case plug in the values and show equation satisfied
  . obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h
    all_goals norm_num