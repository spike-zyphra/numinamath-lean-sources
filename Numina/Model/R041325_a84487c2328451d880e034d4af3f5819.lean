import Mathlib

def D : ℕ → ℤ
| 0 => 0
| 1 => 0
| 2 => 1
| n + 3 => D (n + 2) + D n

theorem number_theory_141425 :
    Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023) := by
  have h1 : (D 2021 : ℤ) % 2 = 0 := by
    have h2 : ∀ (k : ℕ), (D (7 * k + 5) : ℤ) % 2 = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num [D]
      | succ k ih =>
        simp [D, mul_add, add_mul] at ih ⊢
        all_goals
        omega
    specialize h2 288
    norm_num at h2 ⊢
    omega

  have h2 : (D 2022 : ℤ) % 2 = 1 := by
    have h2 : ∀ (k : ℕ), (D (7 * k + 6) : ℤ) % 2 = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num [D]
      | succ k ih =>
        simp [D, mul_add, add_mul] at ih ⊢
        all_goals
        omega
    specialize h2 288
    norm_num at h2 ⊢
    omega

  have h3 : (D 2023 : ℤ) % 2 = 0 := by
    have h2 : ∀ (k : ℕ), (D (7 * k + 0) : ℤ) % 2 = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num [D]
      | succ k ih =>
        simp [D, mul_add, add_mul] at ih ⊢
        all_goals
        omega
    specialize h2 289
    norm_num at h2 ⊢
    omega

  constructor
  · -- Show that D 2021 is even
    exact ⟨(D 2021) / 2, by omega⟩
  constructor
  · -- Show that D 2022 is odd
    exact ⟨(D 2022) / 2, by omega⟩
  · -- Show that D 2023 is even
    exact ⟨(D 2023) / 2, by omega⟩