import Mathlib

def SetOfInts := ({4, 9, 12, 16, 18} : Finset ℕ)

theorem number_theory_230 :
    IsLeast {x | ∃ a b : SetOfInts, a ≠ b ∧ x = Nat.gcd a.val b.val + Nat.lcm a.val b.val} 16 := by
  constructor
  · -- Show 16 is achievable, using 4 and 12
    use ⟨4, by simp [SetOfInts]⟩, ⟨12, by simp [SetOfInts]⟩
    all_goals
      native_decide
  · -- Show there is no smaller value in the set
    intro x hx
    rcases hx with ⟨a, b, hne, heq⟩
    fin_cases a <;> fin_cases b <;> simp [SetOfInts] at hne ⊢ <;> try { 
      all_goals 
        norm_num [heq] at *
        <;> try { 
          all_goals 
            omega 
        }
    }