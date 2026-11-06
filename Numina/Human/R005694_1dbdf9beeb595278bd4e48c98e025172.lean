import Mathlib
open Set Nat Fin
set_option maxRecDepth 500000
noncomputable section

/-Each cell of a $2 \times 5$ grid of unit squares is to be colored white or black. Compute the number of such colorings for which no $2 \times 2$ square is a single color.-/
theorem combinatorics_609459 :
    Fintype.card { c : Fin 2 → Fin 5 → Bool | ∀ i : Fin 4,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 634 := by
  -- Calculate the number of valid colorings for a $2×1$ grid.
  have h1 : Fintype.card { c : Fin 2 → Fin 1 → Bool | ∀ i : Fin 0,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 4 := by
    have : ∀ c : Fin 2 → Fin 1 → Bool, ∀ i : Fin 0, (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
        (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true := by
      intro c i; exact Fin.elim0 i
    simp [this, Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
    tauto

  -- Calculate the number of valid colorings for a $2×2$ grid.
  have h2 : Fintype.card { c : Fin 2 → Fin 2 → Bool | ∀ i : Fin 1,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 14 := by rfl

  -- Calculate the number of valid colorings for a $2×3$ grid.
  have h4 : Fintype.card { c : Fin 2 → Fin 3 → Bool | ∀ i : Fin 2,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 50 := by rfl

  -- Calculate the number of valid colorings for a $2×4$ grid.
  have h5 : Fintype.card { c : Fin 2 → Fin 4 → Bool | ∀ i : Fin 3,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 178 := by rfl

  -- Calculate the number of valid colorings for a $2×5$ grid.
  have h6 : Fintype.card { c : Fin 2 → Fin 5 → Bool | ∀ i : Fin 4,
      (c 0 i && c 0 (i + 1) && c 1 i && c 1 (i + 1)) = false ∧
      (c 0 i || c 0 (i + 1) || c 1 i || c 1 (i + 1)) = true } = 634 := by rfl

  exact h6
