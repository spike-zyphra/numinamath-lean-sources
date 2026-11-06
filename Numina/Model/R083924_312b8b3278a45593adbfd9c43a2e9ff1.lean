import Mathlib

theorem number_theory_228135 {f : Fin 33 → Fin 33} (hf : ∀ x y, f x = f y → x = y) :
    ∃ N, ∀ x, f^[N] x = x := by
  exact ⟨0, fun x => rfl⟩