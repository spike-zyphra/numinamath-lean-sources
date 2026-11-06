import Mathlib

theorem number_theory_128203 :
    ∃ a : ℕ → ℕ,
      (∀ i ∈ Finset.Icc 3 1989, a i + ∑ j in Finset.Icc 1 i, a j = Nat.gcd (a i) (∑ j in Finset.Icc 1 i, a j) + Nat.lcm (a i) (∑ j in Finset.Icc 1 i, a j)) ∧
      a 1 = 1 ∧ a 2 = 2 ∧ ∀ i ≥ 3, a i = 2 ^ (i - 3) * 3 := by 
        use fun i => match i with
          | 0 => 0
          | 1 => 1
          | 2 => 2
          | i + 3 => 2 ^ (i) * 3
        constructor
        . intro i hi
          rw [Finset.mem_Icc] at hi
          rcases hi with ⟨hi3, hi1989⟩
          interval_cases i <;> try native_decide
        constructor
        . -- Verify that a 1 = 1
          native_decide
        constructor
        . -- Verify that a 2 = 2
          native_decide
        . -- Show that ∀ i ≥ 3, a i = 2 ^ (i - 3) * 3
          intro i hi
          cases i with
          | zero => -- contradiction
            exfalso
            linarith 
          | succ i =>
            cases i with
            | zero =>
              exfalso
              linarith
            | succ i =>
              cases i with
              | zero =>
                exfalso
                linarith
              | succ i =>
                simp [show i + 3 = i + 3 by omega]
                <;> omega