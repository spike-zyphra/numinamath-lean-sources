import Mathlib

theorem number_theory_227742 (x : ℕ) (hx : x ∈ Finset.Icc 10 99) :
    2701 % x = 0 ↔ ∑ i ∈ Finset.range 2, (Nat.digits 10 x)[i]!^2 = 58 := by 
  rw [Finset.mem_Icc] at hx
  rcases hx with ⟨h₁, h₂⟩
  interval_cases x <;> norm_num
  <;> all_goals native_decide