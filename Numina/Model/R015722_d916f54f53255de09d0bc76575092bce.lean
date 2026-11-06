import Mathlib

theorem number_theory_133095 (a b c d : ℤ) (h : ∀ m n : ℤ, ∃ h k : ℤ, a * h + b * k = m ∧ c * h + d * k = n) :
    |a * d - b * c| = 1 := by
  have h10 : ∃ h1 k1 : ℤ, a * h1 + b * k1 = 1 ∧ c * h1 + d * k1 = 0 := by
    apply h 1 0
  have h01 : ∃ h2 k2 : ℤ, a * h2 + b * k2 = 0 ∧ c * h2 + d * k2 = 1 := by
    apply h 0 1
  rcases h10 with ⟨h1, k1, eq1, eq2⟩
  rcases h01 with ⟨h2, k2, eq3, eq4⟩
  have eq6 : (a * d - b * c) * (h1 * k2 - h2 * k1) = 1 := by
    nlinarith
  have eq8 : (a * d - b * c) = 1 ∨ (a * d - b * c) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact eq6
  cases eq8 with
  | inl h11 =>
    rw [h11]
    all_goals norm_num
    all_goals tauto
  | inr h11 =>
    rw [h11]
    all_goals norm_num
    all_goals tauto