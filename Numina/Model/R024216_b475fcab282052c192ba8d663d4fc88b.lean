import Mathlib

theorem number_theory_5055 :
    {x : Fin 156 | 2^x.val ≡ x.val [MOD 13]} =
    {10, 16, 57, 59, 90, 99, 115, 134, 144, 145, 149, 152} := by
  ext x
  simp [Finset.mem_insert, Finset.mem_singleton]
  fin_cases x <;> native_decide