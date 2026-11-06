import Mathlib

theorem algebra_250383 {a b c N : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (hN : 0 < N) :
    Real.logb a N * Real.logb b N + Real.logb b N * Real.logb c N + Real.logb c N * Real.logb a N =
    Real.logb a N * Real.logb b N * Real.logb c N / Real.logb (a * b * c) N := by 
  have h1 : Real.logb a N = Real.log N / Real.log a := by 
    field_simp [Real.logb]
  have h2 : Real.logb b N = Real.log N / Real.log b := by
    field_simp [Real.logb]
  have h3 : Real.logb c N = Real.log N / Real.log c := by
    field_simp [Real.logb]
  have h4 : Real.logb (a * b * c) N = Real.log N / Real.log (a * b * c) := by 
    field_simp [Real.logb]
  have h5 : Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by
    simp [Real.log_mul, ha.1.ne.symm, hb.1.ne.symm, hc.1.ne.symm]
  by_cases hN1 : N = 1
  · -- If N = 1, then $\log N = 0$, so both sides are 0
    rw [hN1]
    simp [h1, h2, h3, h4, h5, Real.log_one]
  · -- Assume N ≠ 1
    have h6 : Real.log a ≠ 0 := by
      have h9 : a > 0 := ha.1
      have h8 : a ≠ 1 := ha.2
      exact Real.log_ne_zero_of_pos_of_ne_one h9 h8
    have h7 : Real.log b ≠ 0 := by
      have h9 : b > 0 := hb.1
      have h8 : b ≠ 1 := hb.2
      exact Real.log_ne_zero_of_pos_of_ne_one h9 h8
    have h8 : Real.log c ≠ 0 := by
      have h9 : c > 0 := hc.1
      have h8 : c ≠ 1 := hc.2
      exact Real.log_ne_zero_of_pos_of_ne_one h9 h8
    have h9 : Real.log N ≠ 0 := by
      have h14 : N > 0 := hN
      have h14' : N ≠ 1 := by 
        intro h
        apply hN1
        all_goals linarith
      have h9 : Real.log N ≠ 0 := by
        have h9 : N > 0 := hN
        have h12 : N ≠ 1 := h14'
        exact Real.log_ne_zero_of_pos_of_ne_one h9 h12
      exact h9
    rw [h1, h2, h3, h4, h5]
    field_simp [h6, h7, h8, h9]
    <;> ring_nf