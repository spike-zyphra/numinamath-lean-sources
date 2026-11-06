import Mathlib

theorem algebra_197044 {P : ℕ} (hP : P ∈ Finset.Icc 10 99) (h : (Nat.digits 10 (P ^ 50)).length = 69) :
    P = 23 := by
  rw [Finset.mem_Icc] at hP 
  rcases hP with ⟨hP1, hP2⟩ 
  interval_cases P <;> norm_num at h ⊢ <;> all_goals omega