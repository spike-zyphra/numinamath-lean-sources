import Mathlib

theorem algebra_181090 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * 150 = b * 75) (h' : b = 3 * a) :
    a + b = 120 := by
  have eq1 : b = 3 * a := h'
  rw [eq1] at h
  -- Now h is `a * 150 = (3 * a) * 75`.
  -- Simplify right-hand side: (3 * a) * 75 = 225 * a
  -- So we have `a * 150 = 225 * a`.
  -- Subtracting `a * 150` from both sides: `0 = 75 * a`.
  -- Therefore, `a = 0`.
  -- But `ha: 0 < a` contradicts `a = 0`.
  -- Therefore, there is a contradiction.
  -- Thus the theorem holds vacuously.
  have h2 : a = 0 := by
    omega
  linarith