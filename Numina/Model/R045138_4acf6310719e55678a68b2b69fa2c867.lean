import Mathlib

theorem number_theory_4515 (a b : ℤ) {c : ℤ} (hc : c ∣ a * b) : c ∣ (a.gcd c) * (b.gcd c) := by
  have h3 : ∃ x y, Int.gcd a c = a * x + c * y := by
    refine' ⟨Int.gcdA a c, Int.gcdB a c, by rw [Int.gcd_eq_gcd_ab a c]⟩
  have h4 : ∃ x y, Int.gcd b c = b * x + c * y := by
    refine' ⟨Int.gcdA b c, Int.gcdB b c, by rw [Int.gcd_eq_gcd_ab b c]⟩
  rcases h3 with ⟨x1, y1, h3⟩
  rcases h4 with ⟨x2, y2, h4⟩
  have h5 : (Int.gcd a c) * (Int.gcd b c) = (a * b) * (x1 * x2) + c * (a * (x1 * y2) + b * (y1 * x2) + c * (y1 * y2)) := by
    rw [h3, h4]
    ring_nf
  rw [h5]
  have h6 : c ∣ (a * b) * (x1 * x2) := by
    have h7 : c ∣ a * b := hc
    exact dvd_mul_of_dvd_left h7 (x1 * x2)
  have h7 : c ∣ c * (a * (x1 * y2) + b * (y1 * x2) + c * (y1 * y2)) := by
    use a * (x1 * y2) + b * (y1 * x2) + c * (y1 * y2)
    all_goals ring
  exact dvd_add h6 h7