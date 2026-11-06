import Mathlib

def f (n : ℕ) := n - (Nat.digits 10 n).sum

theorem number_theory_115989 :
    IsLeast {x | ∃ n, x = f^[n] x} 0 := by
  constructor
  · -- Show 0 is in the set
    use 1
    simp [f]
    all_goals omega
  · -- Show there's no smaller element in the set
    intro x hx
    rcases hx with ⟨n, hn⟩
    have hx2 : x >= 0 := by
      omega
    linarith