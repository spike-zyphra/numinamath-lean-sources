import Mathlib

theorem algebra_97298 (n : ℕ) (hn : n > 0) (a b : ℕ)
    (ha : a = b + n) (hb : b > 0) (h1 : a - 1 = 5 * (b - 1)) (h2 : a = (b ^ 2)) :
    n = 12 := by
  have h3 : b ≥ 1 := by linarith
  rw [h2] at h1
  by_cases h4 : b ≤ 1
  · -- b ≤ 1 and b ≥ 1 implies b = 1
    have hb_eq_1 : b = 1 := by linarith
    rw [hb_eq_1] at h1 h2 ha
    omega
  · -- b > 1
    have h5 : b ≥ 2 := by omega
    have eq1 : b ^ 2 + 4 = 5 * b := by
      -- converting h1 into a quadratic equation
      -- b^2 - 5 * b + 4 = 0
      -- To convert subtraction in h1 to addition:
      omega
    -- factoring the quadratic: (b - 1)(b - 4) = 0
    have h6 : b = 4 := by
      -- solving the quadratic equation with constraint b > 1
      nlinarith [eq1]
    -- if b = 4, from h6 and h2:
    have ha_eq : a = 16 := by
      rw [h6] at h2
      nlinarith
    -- from ha: a = b + n => 16 = 4 + n => n = 12
    rw [ha_eq, h6] at ha
    omega