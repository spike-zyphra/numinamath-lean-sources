import Mathlib

/-A4. How many positive integers $N$ of two digits are there with the following property: The sum of $N$ and the reverse of $N$ is a square of an integer (the reverse of $N$ is the number you get by writing $N$ backwards)?-/
theorem number_theory_174908 : Set.ncard {N : ℕ | N ∈ Finset.Icc 10 99 ∧ IsSquare (N + (N % 10) * 10 + N / 10)} = 8 := by
  have : {N : ℕ | N ∈ Finset.Icc 10 99 ∧ IsSquare (N + (N % 10) * 10 + N / 10)} = ({29,38,47,56,65,74,83, 92} : Finset ℕ) := by
    ext x; simp only [Finset.mem_Icc, Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂⟩
      obtain ⟨a, b, ha₁, hb₁⟩ := show ∃a b, a = x / 10 ∧ b = x % 10 by simp
      rw [show x + x % 10 * 10 + x / 10 = 11 * (a + b) by omega] at hx₂
      have hab : a + b = 11 := by
        set c := a + b with hc
        have hc₁ : c ≤ 18 := by omega
        have hc₂ : 1 ≤ c := by omega
        by_contra! h
        revert hx₂
        interval_cases c
          <;> simp at h
          <;> native_decide
      rw [show x = 9 * a + 11 by omega]
      simp only [Nat.reduceEqDiff]
      omega
    · intro h
      obtain (h | h | h | h | h | h | h | h) := h <;> rw [h]
      all_goals native_decide
  rw [this, Set.ncard_coe_Finset]
  simp
