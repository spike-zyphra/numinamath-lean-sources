import Mathlib
set_option maxRecDepth 5000

/--
PROBLEM: For how many positive integers m is
2002/(m^2−2)
a positive integer?
-/
theorem AMC_Number_Theory_1140 (m : ℕ) : (m^2 - 2) ∣ 2002 ↔ m ∈ ({2,3,4} : Finset ℕ) := by {
  -- Show right implication first
  constructor
  intro hl
  have hl1 : ((m^2 - 2) ∣ 2002) ∧ (2002 ≠ 0) := by {
    constructor
    exact hl
    trivial
  }
  rw [←Nat.mem_divisors] at hl1
  
  -- reduce to this finite set of cases by listing all the divisors of 2002
  have hl2 : (m^2 - 2) ∈ ({1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} : Finset ℕ) := by exact hl1
  simp at hl2

  have haux (a b c : ℕ) : (c ≠ 0) → (a - b = c) → (a = c + b) := by {
    intro h h'
    by_cases h'' : b ≤ a
    rw [←Nat.sub_eq_iff_eq_add h'']
    exact h'
    simp at h''
    apply le_of_lt at h''
    rw [←Nat.sub_eq_zero_iff_le,h'] at h''
    contradiction
  }

  -- Go through each case
  rcases hl2 with ha1 | ha2 | ha7 | ha11 | ha13 | ha14 | ha22 | ha26 | ha77 | ha91 | ha143 | ha154 | ha182 | ha286 | ha1001 | ha2002
  -- Exhaustive case analysis for each possible divisor
  absurd ha1
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 3 := by {
    apply Nat.not_exists_sq' _ _
    use 1
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial
  
  
  suffices : m = 2
  rw [this]; trivial
  rw [←Nat.mul_self_inj,←pow_two]
  apply haux at ha2
  trivial
  trivial

  suffices : m = 3
  rw [this]; trivial
  rw [←Nat.mul_self_inj,←pow_two]
  apply haux at ha7
  trivial
  trivial

  absurd ha11
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 13 := by {
    apply Nat.not_exists_sq' _ _
    use 3
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha13
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 15 := by {
    apply Nat.not_exists_sq' _ _
    use 3
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial
  
  suffices : m = 4
  rw [this]; trivial
  rw [←Nat.mul_self_inj,←pow_two]
  apply haux at ha14
  trivial
  trivial

  absurd ha22
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 24 := by {
    apply Nat.not_exists_sq' _ _
    use 4
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha26
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 28 := by {
    apply Nat.not_exists_sq' _ _
    use 5
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha77
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 79 := by {
    apply Nat.not_exists_sq' _ _
    use 8
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha91
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 93 := by {
    apply Nat.not_exists_sq' _ _
    use 9
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha143
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 145 := by {
    apply Nat.not_exists_sq' _ _
    use 12
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha154
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 156 := by {
    apply Nat.not_exists_sq' _ _
    use 12
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha182
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 184 := by {
    apply Nat.not_exists_sq' _ _
    use 13
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha286
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 288 := by {
    apply Nat.not_exists_sq' _ _
    use 16
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha1001
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 1003 := by {
    apply Nat.not_exists_sq' _ _
    use 31
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  absurd ha2002
  have hnotsq : ¬ ∃ k : ℕ, k^2 = 2004 := by {
    apply Nat.not_exists_sq' _ _
    use 44
    trivial
    trivial
  }
  simp at hnotsq
  have := hnotsq m
  contrapose! this
  apply haux at this
  exact this
  trivial

  -- Show left implication
  intro hr
  rw [Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with hr1 | hr2 | hr3
  rw [hr1]; trivial
  rw [hr2]; trivial
  rw [hr3]; trivial
}