import Mathlib

theorem algebra_199218 (x y z : ℕ) (h₀ : x + y + z ≤ 200)
    (h₁ : y = 4 * x) (h₂ : z % x = 0) (h₃ : z * 5 = y + 99) :
    x = 9 ∧ y = 36 ∧ z = 27 := by
  have eq1 : y = 4 * x := h₁
  have eq2 : z * 5 = 4 * x + 99 := by
    rw [show y = 4 * x by omega] at h₃
    omega
  have h4 : x ≤ 31 := by
    omega
  have h5 : x ≤ 31 := h4
  interval_cases x <;> try { 
    omega 
  }
  <;> try { 
    interval_cases z <;> norm_num [eq1] at *
    <;> omega 
  }