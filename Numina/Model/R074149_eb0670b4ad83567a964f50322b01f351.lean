import Mathlib

theorem number_theory_34971 (a b : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (h : Nat.gcd a b = 6) :
    a + b ≤ 186 := by
  rw [Finset.mem_Icc] at ha hb
  rcases ha with ⟨ha10, ha99⟩
  rcases hb with ⟨hb10, hb99⟩
  by_contra h'
  push_neg at h'
  interval_cases a <;> interval_cases b
  <;> norm_num [Nat.gcd] at h h'
  all_goals omega