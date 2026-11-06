import Mathlib

theorem algebra_176830 {A B : ℕ} (hA : A ∈ Finset.Icc 10 99) (hB : B ∈ Finset.Icc 10 99)
    (h1 : (100 * A + B) / B = 121) (h2 : (100 * B + A) / A = 84 ∧ (100 * B + A) % A = 14) :
    A = 42 ∧ B = 35 := by
  rw [Finset.mem_Icc] at hA hB
  rcases h2 with ⟨h21, h22⟩
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  interval_cases A <;> interval_cases B <;> norm_num at h1 h21 h22 
    <;> tauto