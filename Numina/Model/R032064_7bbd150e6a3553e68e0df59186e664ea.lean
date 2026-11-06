import Mathlib

theorem algebra_20669 {f g : Polynomial ℝ} (hf : f.degree = 3) (hg : g.degree = 5) :
    (2 * f + 4 * g).degree = 5 := by
  have h1 : (Polynomial.C (2 : ℝ) * f).degree = 3 := by 
    rw [Polynomial.degree_mul]
    all_goals simp [hf]
    <;> norm_num

  have h2 : (Polynomial.C (4 : ℝ) * g).degree = 5 := by 
    rw [Polynomial.degree_mul]
    all_goals simp [hg]
    <;> norm_num

  have h3 : ((Polynomial.C (2 : ℝ) * f) + (Polynomial.C (4 : ℝ) * g)).degree = 5 := by 
    have h4 : (Polynomial.C (2 : ℝ) * f).degree < (Polynomial.C (4 : ℝ) * g).degree := by 
      rw [h1, h2]
      all_goals norm_num 
    rw [Polynomial.degree_add_eq_right_of_degree_lt h4]
    <;> simp [h1, h2]

  have h4 : (2 * f + 4 * g : Polynomial ℝ) = (Polynomial.C (2 : ℝ) * f + Polynomial.C (4 : ℝ) * g) := by 
    ring_nf 
    <;> rfl
  rw [h4]
  exact h3