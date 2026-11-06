import Mathlib

open Finset

theorem other_60275 {n : ℕ} (hn : 0 < n) (f : Equiv.Perm (Fin n)) :
    ∃ M : ℕ, 0 < M ∧ ∀ i : Fin n, f^[M] i = f i := by
  use 1
  constructor
  · -- Show that M is positive
    norm_num
  · -- Show that f^[1] i = f i for all i : Fin n
    intro i
    simp