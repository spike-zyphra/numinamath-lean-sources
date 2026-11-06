import Mathlib

theorem number_theory_15624 : IsGreatest {m : ℕ | m ∈ Finset.Icc 100 999 ∧ ∃(x y : ℕ), x.Prime ∧ y.Prime ∧ x < 10 ∧ y < 10 ∧ x ≠ y ∧ (10 * x + y).Prime ∧ m = x * y * (10 * x + y)} 795 := by
  constructor
  · -- Show 795 is in the set
    constructor
    · -- Show 795 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show exist x y such that 795 = x * y * (10 * x + y)
      use 5, 3
      constructor
      · -- Show x = 5 is prime
        norm_num
      constructor
      · -- Show y = 3 is prime
        norm_num
      constructor
      · -- Show x < 10
        norm_num
      constructor
      · -- Show y < 10
        norm_num
      constructor
      · -- Show x ≠ y
        norm_num
      constructor
      · -- Show that 10 * 5 + 3 = 53 is prime
        norm_num
      · -- Show that 795 = 5 * 3 * 53
        norm_num
  · -- Show there is no greater element in the set
    intro m hm
    rcases hm with ⟨hm1, x, y, hx, hy, hx10, hy10, hxy, h10xy, hm⟩
    rw [Finset.mem_Icc] at hm1
    rcases hm1 with ⟨mge100, mle999⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 9 := by linarith
    have h2 : y ≤ 9 := by linarith
    interval_cases x <;> interval_cases y
    <;> norm_num [Nat.mul_comm] at hx hy h10xy hm hxy
    <;> omega