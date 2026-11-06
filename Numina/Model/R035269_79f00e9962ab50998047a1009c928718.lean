import Mathlib

theorem algebra_287161 :
  {n : ℕ | n > 0 ∧ ∃ p : ℝ, p > 0 ∧
    (n - 40 : ℝ) + 40 * p = 1.2 * n ∧
    (0.4 * n : ℝ) + 0.6 * n * p = 2.5 * n} =
  {500} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h, proving n=500
    intro h 
    rcases h with ⟨hn_pos, p, hp_pos, heq1, heq2⟩ 
    have eq1 : (n : ℝ) > (0 : ℝ) := by 
      exact_mod_cast hn_pos
    have eq1' : (n : ℝ) - 40 + 40 * p = (1.2 : ℝ) * (n : ℝ) := by 
      linarith 
    ring_nf at eq1'
    have eq2' : (0.4 : ℝ) * (n : ℝ) + (0.6 : ℝ) * (n : ℝ) * p = (2.5 : ℝ) * (n : ℝ) := by 
      linarith 
    ring_nf at eq2'
    have hne : (n : ℝ) ≠ 0 := by
      have hn_pos' : (n : ℝ) > (0 : ℝ) := by
        exact_mod_cast hn_pos
      nlinarith 
    have hp : p = (3.5 : ℝ) := by
      apply (mul_left_inj' hne).mp
      linarith 
    rw [hp] at eq1'
    have hn_eq500 : (n : ℝ) = 500 := by 
      nlinarith 
    have hn_nat : n = 500 := by 
      exact_mod_cast hn_eq500 
    exact_mod_cast hn_nat 
  · -- Assume n=500, proving h
    intro h_eq
    rw [h_eq]
    constructor 
    · -- Show n > 0 
      norm_num 
    · -- Show there exists p
      use (3.5 : ℝ)
      constructor 
      · -- Show p > 0 
        norm_num 
      constructor 
      · -- First equation 
        norm_num 
      · -- Second equation 
        norm_num