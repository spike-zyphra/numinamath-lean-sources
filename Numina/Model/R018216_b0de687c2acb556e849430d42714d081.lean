import Mathlib

theorem number_theory_153941 {a b c : ℤ} (h : a.gcd b = 1) (x₁ x₂ y₁ y₂ : ℤ)
    (h₁ : a * x₁ + b * y₁ = c) (h₂ : a * x₂ + b * y₂ = c) (h₃ : x₁ = x₂ + 1) :
    |b| = 1 ∧ |a| = |y₂ - y₁| := by
  have eq1 : a * x₁ + b * y₁ = a * x₂ + b * y₂ := by 
    linarith
  have eq2 : a * (x₁ - x₂) = b * (y₂ - y₁) := by
    linarith [eq1]
  have eq3 : x₁ - x₂ = 1 := by
    linarith [h₃]
  have eq4 : a = b * (y₂ - y₁) := by
    rw [eq3] at eq2
    linarith
  have h4 : b ∣ a := by 
    use y₂ - y₁
    all_goals linarith [eq4]
  have h5 : b ∣ a.gcd b := by
    apply Int.dvd_gcd
    · -- Show that b divides a
      exact h4
    · -- Show that b divides b
      simp
  have h6 : b ∣ 1 := by 
    rw [h] at h5
    exact h5
  have h7 : b = 1 ∨ b = -1 := by
    have : b ∣ 1 := h6
    have h8 : b ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) this
    have h9 : b ≥ -1 := by 
      have h10 : (-b) ∣ 1 := by
        exact Int.neg_dvd.2 this
      have h11 : -b ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h10
      have h12 : b ≥ -1 := by
        linarith
      linarith
    interval_cases b <;> tauto
  have h8 : |b| = 1 := by
    cases h7 with
    | inl h2 =>
      rw [h2]
      all_goals norm_num
    | inr h2 =>
      rw [h2]
      all_goals norm_num
  have h9 : |a| = |b| * |y₂ - y₁| := by
    have h2 : a = b * (y₂ - y₁) := by
      linarith [eq4]
    rw [h2]
    rw [abs_mul]
  have h10 : |a| = |y₂ - y₁| := by 
    rw [h9]
    rw [h8]
    all_goals norm_num
    all_goals linarith
  exact ⟨h8, h10⟩