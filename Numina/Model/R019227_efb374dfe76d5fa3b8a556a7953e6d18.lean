import Mathlib

theorem number_theory_326059 {A G : ℕ} (hA : A = (98 + 32) / 2) (hG : G = √(98 * 32)) :
    A ∈ Finset.Icc 10 99 ∧ G ∈ Finset.Icc 10 99 ∧ ∃ p q r s : ℕ, A = 10 * p + q ∧ G = 10 * r + s ∧
    p = s ∧ q = r := by

  have hA' : A = 65 := by
    norm_num [hA]

  have hG1 : G = 56 := by 
    have h2 : (G : ℝ) = √(98 * 32 : ℝ) := by
      exact_mod_cast hG

    have h3 : √(98 * 32 : ℝ) = (56 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

    have h4 : (G : ℝ) = (56 : ℝ) := by 
      rw [h3] at h2
      linarith

    have h5 : G = (56 : ℕ) := by 
      exact_mod_cast h4

    exact h5

  rw [hA', hG1]
  constructor
  · -- Show 65 ∈ Finset.Icc 10 99
    simp
  constructor
  · -- Show 56 ∈ Finset.Icc 10 99
    simp
  · -- Show ∃ p q r s : ℕ, 65 = 10 * p + q ∧ 56 = 10 * r + s ∧ p = s ∧ q = r
    refine' ⟨6, 5, 5, 6, ?_, ?_, ?_, ?_⟩
    all_goals norm_num