import Mathlib

open Int

theorem number_theory_4649 {a b : ℤ} (hb : 0 < b) : ∃! qr : ℤ × ℤ, a = b*qr.1 + qr.2 ∧ qr.2 ∈ Finset.Ico 0 b := by
  use (a / b, a % b)
  simp_all
  constructor
  -- prove that `q=a/b` and `r=a%b` satify `a=bq+r` and `0 ≤ r < b`
  · split_ands
    -- exact `Int.emod_add_ediv` in Mathlib
    · have := Int.emod_add_ediv a b
      rw [add_comm, Eq.comm] at this
      exact this
    · exact Int.emod_nonneg a (by linarith)
    · exact Int.emod_lt_of_pos a hb
  -- prove the uniqueness
  · intro q r h hr hrb
    -- exact `Int.ediv_emod_unique` in Mathlib
    have := (Int.ediv_emod_unique hb).mpr ⟨(show r + b * q = a by linarith),hr,hrb⟩
    split_ands <;> rw [← h]
    · exact Eq.symm <| this.1
    · exact Eq.symm <| this.2
