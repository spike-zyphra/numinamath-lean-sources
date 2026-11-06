import Mathlib

theorem algebra_197147 {x1 x2 A : ℂ} (hx1 : x1 ≠ x2) (h1 : x1 * (x1 + 1) = A) (h2 : x2 * (x2 + 1) = A)
    (h3 : x1^4 + 3 * x1^3 + 5 * x1 = x2^4 + 3 * x2^3 + 5 * x2) :
    A = -7 := by
  have eq1 : x1^2 = A - x1 := by
    calc
      x1^2 = (x1 * (x1 + 1)) - x1 := by ring_nf
      _ = A - x1 := by rw [h1]
  have eq2 : x2^2 = A - x2 := by
    calc
      x2^2 = (x2 * (x2 + 1)) - x2 := by ring_nf
      _ = A - x2 := by rw [h2]
  have eq3 : x1^3 = (A + 1) * x1 - A := by
    calc
      x1^3 = x1 * x1^2 := by ring_nf
      _ = x1 * (A - x1) := by rw [eq1]
      _ = A * x1 - x1^2 := by ring_nf
      _ = A * x1 - (A - x1) := by rw [eq1]
      _ = (A + 1) * x1 - A := by ring_nf
  have eq4 : x1^4 = (A^2 + A) - (2 * A + 1) * x1 := by
    calc
      x1^4 = (x1^2) ^ 2 := by ring_nf
      _ = (A - x1) ^ 2 := by rw [eq1]
      _ = A^2 - 2 * A * x1 + x1^2 := by ring_nf
      _ = A^2 - 2 * A * x1 + (A - x1) := by rw [eq1]
      _ = (A^2 + A) - (2 * A + 1) * x1 := by ring_nf
  have eq5 : x2^3 = (A + 1) * x2 - A := by
    calc
      x2^3 = x2 * x2^2 := by ring_nf
      _ = x2 * (A - x2) := by rw [eq2]
      _ = A * x2 - x2^2 := by ring_nf
      _ = A * x2 - (A - x2) := by rw [eq2]
      _ = (A + 1) * x2 - A := by ring_nf
  have eq6 : x2^4 = (A^2 + A) - (2 * A + 1) * x2 := by
    calc
      x2^4 = (x2^2) ^ 2 := by ring_nf
      _ = (A - x2) ^ 2 := by rw [eq2]
      _ = A^2 - 2 * A * x2 + x2^2 := by ring_nf
      _ = A^2 - 2 * A * x2 + (A - x2) := by rw [eq2]
      _ = (A^2 + A) - (2 * A + 1) * x2 := by ring_nf
  have eq7 : x1^4 + 3 * x1^3 + 5 * x1 = (A + 7) * x1 + (A^2 - 2 * A) := by
    rw [eq4, eq3]
    ring_nf
  have eq8 : x2^4 + 3 * x2^3 + 5 * x2 = (A + 7) * x2 + (A^2 - 2 * A) := by
    rw [eq6, eq5]
    ring_nf
  rw [eq7] at h3
  rw [eq8] at h3
  have eq10 : (A + 7) * (x1 - x2) = 0 := by
    calc
      (A + 7) * (x1 - x2) = (A + 7) * x1 - (A + 7) * x2 := by ring_nf
      _ = ((A + 7) * x1 + (A ^ 2 - 2 * A)) - ((A + 7) * x2 + (A ^ 2 - 2 * A)) := by 
        ring_nf
      _ = 0 := by 
        rw [h3]
        simp
  cases' (mul_eq_zero.1 eq10) with eq11 eq12
  · -- Case A + 7 = 0, so A = -7
    have : A = -7 := by
      calc
        A = (A + 7) - 7 := by ring_nf
        _ = (0) - 7 := by rw [eq11]
        _ = -7 := by ring_nf
    exact_mod_cast this
  · -- Case x1 - x2 = 0, so x1 = x2
    exfalso 
    apply hx1 
    exact_mod_cast (eq_of_sub_eq_zero eq12)