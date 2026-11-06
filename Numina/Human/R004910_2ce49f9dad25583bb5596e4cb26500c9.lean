import Mathlib

/-Along a round table are arranged 11 cards with the names (all distinct) of the 11 members of the $16^{\text {th }}$ JBMO Problem Selection Committee. The distances between each two consecutive cards are equal. Assume that in the first meeting of the Committee none of its 11 members sits in front of the card with his name. Is it possible to rotate the table by some angle so that at the end at least two members of sit in front of the card with their names?-/
theorem combinatorics_604573 : ∀ (σ : Fin 11 ≃ Fin 11), (∀ i, σ i ≠ i) →
    ∃ k : Fin 11, k ≠ 0 ∧ 1 < Fintype.card { i : Fin 11 | σ (i - k) = i } := by
  intro σ h_derange
  -- Define the set of non-zero rotations ($k ≠ 0$ in Fin $11$).
  let Nonzero := { k : Fin 11 // k ≠ 0 }
  have h_single : Fintype.card { k : Fin 11 // k = 0 } = 1 := by
    rw [Fintype.card_eq_one_iff]
    use ⟨0, rfl⟩
    intro ⟨k, hk⟩
    congr
  have h_card : Fintype.card Nonzero = 10 := by
    rw [Fintype.card_subtype_compl (· = 0)]
    rw [Fintype.card_fin, h_single]
  have h_ne : ∀ i, i ≠ σ.symm i := by
    intro i h
    exact h_derange i (congr_arg σ h ▸ σ.apply_symm_apply i)
  -- Define the function $f$ mapping each member to their "displacement" under σ inverse.
  let f : Fin 11 → Nonzero := λ i ↦ ⟨i - σ.symm i, fun hzero ↦ h_ne i (sub_eq_zero.mp hzero)⟩
  let s : Finset (Fin 11) := Finset.univ
  let t : Finset Nonzero := Finset.univ
  have hc : t.card < s.card := by decide
  have hf : ∀ i ∈ s, f i ∈ t := fun _ _ ↦ Finset.mem_univ _
  -- Apply the pigeonhole principle to find two members with the same displacement.
  have h_pigeon : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hf
  obtain ⟨x, _, y', _, hne, heq⟩ := h_pigeon
  let y := f x
  -- Extract the rotation angle $k$ from the common displacement.
  let k := y.val
  have h_k0 : k ≠ 0 := y.prop
  have h_val_x : x - σ.symm x = k := by rfl
  have h_symm_x : σ.symm x = x - k := by omega
  have h_x_fixed : σ (x - k) = x := by
    rw [← h_symm_x]
    exact σ.apply_symm_apply x
  have h_val_y : y' - σ.symm y' = k := (congr_arg Subtype.val heq).symm
  have h_symm_y : σ.symm y' = y' - k := by omega
  have h_y_fixed : σ (y' - k) = y' := by
    rw [← h_symm_y]
    exact σ.apply_symm_apply y'
  -- Define an injective function from Fin $2$ to the set of fixed points after rotation by $k$.
  let phi : Fin 2 → { i // σ (i - k) = i }
  | 0 => ⟨x, h_x_fixed⟩
  | 1 => ⟨y', h_y_fixed⟩
  have h_inj : Function.Injective phi := fun {a b} h ↦ by
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      exact hne (Subtype.mk_eq_mk.mp h)
    · exfalso
      exact hne.symm (Subtype.mk_eq_mk.mp h)
    · rfl
  -- Prove there are at least two fixed points using injectivity.
  have h_ge_two : 2 ≤ Fintype.card { i // σ (i - k) = i } :=
    Fintype.card_le_of_injective phi h_inj
  have h_lt : 1 < Fintype.card { i // σ (i - k) = i } :=
    Nat.succ_le_iff.mp h_ge_two
  exact ⟨k, h_k0, h_lt⟩
