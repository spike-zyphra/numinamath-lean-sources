import Mathlib

open Real Set
open scoped Real

theorem algebra_168939 (x : ℝ) :
  2 * (sin x ^ 6 + cos x ^ 6) - 3 * (sin x ^ 4 + cos x ^ 4) = cos (2 * x) ↔
  ∃ k : ℤ, x = (π / 2) * (2 * k + 1) := by
  constructor
  · -- Forward direction
    intro h
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by 
      calc
        sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring
        _ = 1 ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by rw [h1]
        _ = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring 
    have h3 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by 
      calc 
        sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by ring
        _ = 1 ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * 1 := by rw [h1]
        _ = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by ring
    have eq1 : 2 * (sin x ^ 6 + cos x ^ 6) - 3 * (sin x ^ 4 + cos x ^ 4) = -1 := by 
      rw [h3, h2]
      linarith 
    have eq2 : cos (2 * x) = -1 := by
      linarith [eq1, h]
    have h4 : ∃ k : ℤ, 2 * x = Real.pi + 2 * Real.pi * k := by
      rw [cos_eq_neg_one_iff] at eq2
      rcases eq2 with ⟨k, hk⟩
      use k
      all_goals 
        try { linarith [hk] }
    rcases h4 with ⟨k, hk⟩
    use k
    have eq3 : x = (Real.pi / 2) * (2 * k + 1) := by
      have eq4 : 2 * x = Real.pi + 2 * Real.pi * k := by
        linarith [hk]
      have eq5 : x = (Real.pi / 2) * (2 * k + 1) := by
        have eq6 : 2 * x = Real.pi + 2 * Real.pi * k := eq4
        have eq7 : x = (Real.pi + 2 * Real.pi * k) / 2 := by 
          linarith 
        rw [eq7]
        field_simp 
        <;> ring 
      linarith [eq5]
    linarith [eq3]
  · -- Backward direction
    rintro ⟨k, hk⟩
    have h1 : x = (Real.pi / 2) * (2 * k + 1) := by
      linarith [hk]
    have h2 : cos (2 * x) = -1 := by
      have eq1 : 2 * x = (k : ℝ) * (2 * Real.pi) + Real.pi := by
        rw [show x = (Real.pi / 2) * (2 * k + 1) by linarith [h1]] 
        ring_nf 
        <;> field_simp 
        <;> ring 
      rw [eq1]
      have eq2 : cos ((k : ℝ) * (2 * Real.pi) + Real.pi) = cos (Real.pi : ℝ) := by
        have h6 : cos ((k : ℝ) * (2 * Real.pi) + Real.pi) = cos (Real.pi) := by
          have : (k : ℝ) * (2 * Real.pi) + Real.pi = Real.pi + (k : ℝ) * (2 * Real.pi) := by ring
          rw [this]
          rw [cos_add_int_mul_two_pi]
          <;> simp [Real.pi] 
          all_goals linarith 
        exact h6
      rw [eq2]
      rw [cos_pi]
      all_goals linarith 
    have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2' : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by 
      calc
        sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring
        _ = 1 ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by rw [h4]
        _ = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring 
    have h3' : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by 
      calc 
        sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by ring
        _ = 1 ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * 1 := by rw [h4]
        _ = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by ring 
    have eq1 : 2 * (sin x ^ 6 + cos x ^ 6) - 3 * (sin x ^ 4 + cos x ^ 4) = -1 := by 
      rw [h3', h2']
      linarith 
    linarith [eq1, h2]