import Mathlib

theorem number_theory_283577 {P Q R k : ℕ} (hP : P > 0) (hQ : Q > 0)
    (hR : R > 0) (hk : k > 0) (h : P * Q = R) :
    (P % k) * (Q % k) % k = R % k := by
  have h1 : (P % k) * (Q % k) % k = (P * Q) % k := by
    simp [Nat.mul_mod]
  have h2 : (P * Q) % k = R % k := by
    rw [h]
  rw [h1, h2]