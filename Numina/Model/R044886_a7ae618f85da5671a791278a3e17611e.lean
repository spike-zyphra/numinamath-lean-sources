import Mathlib

theorem algebra_278364 {a b c p : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hc : 0 < c ∧ c ≠ 1)
    (hp : 0 < p) :
    Real.logb a p * Real.logb b p + Real.logb b p * Real.logb c p + Real.logb a p * Real.logb c p =
    Real.logb a p * Real.logb b p * Real.logb c p / Real.logb (a * b * c) p := by

  have h1 : Real.logb a p = Real.log p / Real.log a := by
    field_simp [Real.logb]
  have h2 : Real.logb b p = Real.log p / Real.log b := by
    field_simp [Real.logb]
  have h3 : Real.logb c p = Real.log p / Real.log c := by
    field_simp [Real.logb]
  have h4 : Real.logb (a * b * c) p = Real.log p / Real.log (a * b * c) := by
    field_simp [Real.logb]

  have h5 : Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by 
    simp [Real.log_mul, ha.1.ne', hb.1.ne', hc.1.ne']

  have h6 : Real.log a ≠ 0 := by
    have h1 : a > 0 := ha.1
    have h2 : a ≠ 1 := ha.2
    exact Real.log_ne_zero_of_pos_of_ne_one h1 h2

  have h7 : Real.log b ≠ 0 := by
    have h1 : b > 0 := hb.1
    have h2 : b ≠ 1 := hb.2
    exact Real.log_ne_zero_of_pos_of_ne_one h1 h2

  have h8 : Real.log c ≠ 0 := by
    have h1 : c > 0 := hc.1
    have h2 : c ≠ 1 := hc.2
    exact Real.log_ne_zero_of_pos_of_ne_one h1 h2

  rw [h1, h2, h3, h4]

  by_cases hp1 : Real.log p = 0
  · -- case where Real.log p = 0, i.e., p = 1
    simp [hp1, h5]
  · -- case where Real.log p ≠ 0
    have hp2 : Real.log p ≠ 0 := by
      intro h
      apply hp1
      linarith 
    field_simp [h6, h7, h8, hp1, h5, hp2]
    <;> ring_nf