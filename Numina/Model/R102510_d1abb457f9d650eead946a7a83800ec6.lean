import Mathlib

def f (n m : ℕ) := Nat.gcd n m

theorem number_theory_117130 :
    IsGreatest {x | ∃ a b, a ≠ b ∧ x = a + b ∧ f a b = 17 ∧ a ∈ Finset.Icc 1000 9999 ∧ b ∈ Finset.Icc 1000 9999} 19975 := by
  constructor
  · -- Show 19975 is in the set
    use 9996, 9979
    constructor
    · norm_num -- Show 9996 ≠ 9979
    constructor
    · norm_num -- Show 19975 = 9996 + 9979
    constructor
    · -- Show f 9996 9979 = 17
      unfold f
      native_decide
    constructor
    · -- Show 9996 ∈ [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 9979 ∈ [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  · -- Show that x is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, hneq, heq, hgcd, ha, hb⟩
    rw [Finset.mem_Icc] at ha hb
    rcases ha with ⟨ha1000, ha9999⟩
    rcases hb with ⟨hb1000, hb9999⟩
    by_contra h
    push_neg at h
    have h1 : a + b > 19975 := by linarith
    have h2 : a ≥ 9977 := by omega
    have h3 : b ≥ 9977 := by omega
    interval_cases a <;> interval_cases b
    <;> norm_num [f] at hgcd
    all_goals
      omega