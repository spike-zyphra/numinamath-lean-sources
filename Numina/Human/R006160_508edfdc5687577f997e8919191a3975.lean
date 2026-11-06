import Mathlib

theorem algebra_625784 : IsLeast {x : ℕ | ∃y, x + y = 176 ∧ ∃m > 1, x + 16 = m * (y - 16) + 31 ∧ y ≥ 16} 131 := by
  constructor
  · simp
    use 45
    norm_num
    use 4
    norm_num
  · intro x hx
    simp at hx
    rcases hx with ⟨y, hy₁, m, hm₁, hm₂, hy₂⟩
    have hy₃ : y - 16 = 160 - x := by omega
    rw [hy₃] at hm₂
    have hx₁ : x ≤ 160 := by omega
    interval_cases x <;> omega
