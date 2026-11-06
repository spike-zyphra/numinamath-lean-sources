import Mathlib

theorem algebra_123213 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hnondeg : a < b + c)
    (h : a > b ∧ b > c) (T : ℕ → ℤ) (hT : ∀ n, T n = (a + b + c) ^ (2 * n) -
    (a - b + c) ^ (2 * n) - (a + b - c) ^ (2 * n) + (a - b - c) ^ (2 * n))
    (hT1 : T 1 ≠ 0) (hT2 : T 2 ≠ 0) (hT3 : T 2 / (2 * T 1) = 2023) :
    a + b + c = 49 := by
  have hT1' : T 1 = 8*b*c := by
    rw [hT 1]
    ring_nf
  have hT2' : T 2 = 16*b*c*(3*a^2 + b^2 + c^2) := by
    rw [hT 2]
    ring_nf
  rw [hT1', hT2'] at hT3
  have : (16 * b * c * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (2 * (8 * b * c))) = (16 * b * c) * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (16 * b * c) := by ring_nf
  rw [this] at hT3
  have : (16 * b * c) * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (16 * b * c) = (3 * a ^ 2 + b ^ 2 + c ^ 2) := by field_simp
  rw [this] at hT3
  have h_eq : 3 * a ^ 2 + b ^ 2 + c ^ 2 = 2023 := by linarith
  have h3 : a < b + c := hnondeg
  have h4 : a ≤ 26 := by nlinarith [h_eq]
  have h5 : b ≤ 33 := by nlinarith [h_eq]
  have h6 : c ≤ 33 := by nlinarith [h_eq]
  have h7 : a > b := h.1
  have h8 : b > c := h.2
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega