import Mathlib
set_option maxRecDepth 5000

theorem AMC_Number_Theory_1140 (m : ℕ) : (m^2 - 2) ∣ 2002 ↔ m ∈ ({2,3,4} : Finset ℕ) := by
  constructor
  · -- Assume that $m^2 - 2$ divides 2002, we need to prove that $m \in \{2,3,4\}$.
    intro h
    have h1 : m ≤ 44 := by
      by_contra h2
      push_neg at h2
      have h2 : m ≥ 45 := by omega
      have h3 : m ^ 2 ≥ 2025 := by nlinarith
      have h4 : m ^ 2 - 2 ≥ 2023 := by
        have h5 : m ^ 2 ≥ 2025 := by nlinarith
        omega
      have h5 : m ^ 2 - 2 ≤ 2002 := by
        apply Nat.le_of_dvd (show 0 < 2002 by norm_num) h
      nlinarith -- contradiction
    interval_cases m <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction: if m in {2,3,4}, then m^2-2 divides 2002
    intro h
    fin_cases h <;> norm_num