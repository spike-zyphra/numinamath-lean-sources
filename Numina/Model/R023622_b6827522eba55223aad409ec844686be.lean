import Mathlib

theorem number_theory_291328 (n : ℕ) :
    n ∈ {x | 13 ∣ x ∧ x = 3000803 ∨ x = 3020303 ∨ x = 3030703 ∨ x = 3050203 ∨ x = 3060603 ∨ x = 3080103 ∨ x = 3090503} ↔
    n = 3000803 ∨ n = 3020303 ∨ n = 3030703 ∨ n = 3050203 ∨ n = 3060603 ∨ n = 3080103 ∨ n = 3090503 := by
  simp only [Set.mem_setOf_eq]
  <;> omega