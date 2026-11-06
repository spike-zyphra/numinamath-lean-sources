import Mathlib

theorem algebra_286073 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h1 : a * b = 2 * a * c) (h2 : a * b = c * d + 1 * a)
    (h3 : a * b = d * c - 4 * a) :
    c / d = 4 := by
  have h1' : b = 2 * c := by
    nlinarith
  have h4 : a * b = 2 * a * c := by linarith [h1]
  have h5 : a * b = c * d + a := by linarith [h2]
  have h6 : a * b + 4 * a = d * c := by
    omega
  have h7 : a > 0 := by linarith [ha]
  -- Now, we proceed to derive further expressions. From h5: `a * b = c * d + a` and h4 `a * b = 2 * a * c`, then:
  -- `2 * a * c = c * d + a`, substituting c * d from h6: `c * d = a * b + 4 * a = 2 * a * c + 4 * a`:
  -- `2 * a * c = (2 * a * c + 4 * a) + a` `2 * a * c = 2 * a * c + 5 * a` `0 = 5 * a` `a = 0`
  -- This contradicts `a > 0`.
  have h9 : c * d = 2 * a * c + 4 * a := by
    nlinarith [h6, h4]
  -- Substitute c * d from h9 into h5:
  -- a * b = (2 * a * c + 4 * a) + a
  -- a * b = 2 * a * c + 5 * a
  -- But from h4: a * b = 2 * a * c
  -- Thus, 2 * a * c = 2 * a * c + 5 * a
  -- 0 = 5 * a
  -- 5 * a = 0 implies a = 0.
  -- This contradicts `a > 0`.
  nlinarith