import Mathlib
theorem number_theory_611220 (A B C D : ℕ) (hA : 0 ≤ A ∧ A ≤ 9) (hB : 0 ≤ B ∧ B ≤ 9) (hC : 0 ≤ C ∧ C ≤ 9) (hD : 0 ≤ D ∧ D ≤ 9) (h : A > B ∧ B > C ∧ C > D) (h1 : A * 10 ^ 3 + B * 10 ^ 2 + C * 10 ^ 1 + D * 10 ^ 0 - (D * 10 ^ 3 + C * 10 ^ 2 + B * 10 ^ 1 + A * 10 ^ 0) = B * 10 ^ 3 + D * 10 ^ 2 + A * 10 ^ 1 + C * 10 ^ 0) : (A, B, C, D) = (7, 6, 4, 1):= by

  have h1' : A * 10 ^ 3 + B * 10 ^ 2 + C * 10 ^ 1 + D * 10 ^ 0 = (D * 10 ^ 3 + C * 10 ^ 2 + B * 10 ^ 1 + A * 10 ^ 0) + (B * 10 ^ 3 + D * 10 ^ 2 + A * 10 ^ 1 + C * 10 ^ 0) := by omega
  rcases h with ⟨h2, h3, h4⟩
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  rcases hD with ⟨hD1, hD2⟩
  have : A ≤ 9 := by linarith
  have : B ≤ 9 := by linarith
  have : C ≤ 9 := by linarith
  have : D ≤ 9 := by linarith
  interval_cases A <;> interval_cases B <;> interval_cases C <;> interval_cases D <;> norm_num [Prod.ext_iff] at h1' ⊢ <;> tauto