import Mathlib

/- What is the largest three-digit integer $n$ that satisfies $$55n\equiv 165\pmod{260}~?$$ -/
theorem number_theory_14863 :
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ 55 * n ≡ 165 [MOD 260]} 991 := by
  refine ⟨?_, fun a h ↦ ?_⟩ <;> simp_all [Nat.ModEq, Nat.ModEq.rfl]
  <;> omega