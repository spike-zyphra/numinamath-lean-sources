import Mathlib

def isTrimorphic (n : ℕ) : Prop := n = 30 * (Nat.digits 10 n).sum

theorem number_theory_130489 :
    {n | n ∈ Finset.Icc 1 999 ∧ isTrimorphic n} = {270} := by
  ext n
  simp [isTrimorphic, Finset.mem_Icc]
  constructor
  · -- Forward direction: Show that if n is in the left side, then n is in the right side
    rintro ⟨⟨hn1, hn2⟩, h⟩
    interval_cases n <;> norm_num at h ⊢ <;> omega
  · -- Backward direction: Show that if n is in the right side, then n is in the left side
    rintro (rfl)
    constructor
    · -- Show that 270 is in the range [1, 999]
      native_decide
    · -- Show that 270 is trimorphic
      native_decide