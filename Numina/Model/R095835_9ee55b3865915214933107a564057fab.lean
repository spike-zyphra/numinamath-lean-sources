import Mathlib

theorem algebra_234886 : ¬ ∃ p : Polynomial ℤ, p.eval 1 = 4 ∧ p.eval 4 = 9 := by 
  intro h
  rcases h with ⟨p, h₁, h₂⟩
  have h3 : (4 - 1 : ℤ) ∣ (p.eval 4 - p.eval 1) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [h₁, h₂] at h3
  norm_num at h3
  all_goals 
    omega