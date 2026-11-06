import Mathlib
open Function Real BigOperators

/- Ruby a effectué une série de mouvements avec son Rubik's cube. (Par exemple, elle peut tourner la face du haut dans le sens des aiguilles d'une montre, puis la face de fond de 180 degrés, puis la face de droite dans le sens contraire des aiguilles d'une montre. Ou n'importe quelle autre série de rotations de faces.) Ensuite elle répète inlassablement la même série de mouvements. Montrer qu'au bout d'un certain nombre de répétitions elle retrouvera la configuration de départ. -/
theorem logic_and_puzzles_607451 {α : Type} [Fintype α] {R : α → α}
  (hR : R.Injective)(h_nonempty : Nonempty α) :
  ∃ n, R^[n] = id := by
  -- The state space is finite, so the sequence of configurations will repeat.
  have h_finite_seq : ∃ n m, n < m ∧ R^[n] = R^[m] := by
    have : Fintype (α → α) := Fintype.ofFinite (α → α)
    let input : Finset (Fin (Fintype.card (α → α) + 1)) := Finset.univ
    have h_card : Fintype.card (α → α) < Fintype.card (Fin (Fintype.card (α → α) + 1)) := by
      rw [Fintype.card_fin]
      linarith
    have : ∃ n m : Fin (Fintype.card (α → α) + 1), n ≠ m ∧ R^[n.val] = R^[m.val] := by
      apply Fintype.exists_ne_map_eq_of_card_lt (fun k => R^[k.val]) h_card
    obtain ⟨n, m, hnm, hnm_eq⟩ := this
    have h_nm_lt : ∃ n' m' : ℕ, n' < m' ∧ R^[n'] = R^[m'] := by
      cases Nat.lt_trichotomy n.val m.val with
      | inl h => exact ⟨n.val, m.val, h, hnm_eq⟩
      | inr h =>
        cases h with
        | inl h =>
          have : n = m := by apply Fin.eq_of_val_eq; exact h
          contradiction
        | inr h => exact ⟨m.val, n.val, h, hnm_eq.symm⟩
    obtain ⟨n', m', hnm_lt, h_eq⟩ := h_nm_lt
    exact ⟨n', m', hnm_lt, h_eq⟩
  -- Find $n < m$ such that $R^[n] = R^[m]$.
  obtain ⟨n, m, hnm, hnm_eq⟩ := h_finite_seq
  -- Prove that $R$ is bijective (injective implies bijective on a finite set).
  have hR_bijective : Bijective R := by
    constructor
    · exact hR
    · apply Finite.injective_iff_surjective.mp
      exact hR
  -- Define the inverse of $R$.
  have hR_inv : ∃ R_inv : α → α, R_inv ∘ R = id ∧ R ∘ R_inv = id := by
    exists Function.invFun R
    constructor
    · ext x
      simp only [id_eq, comp_apply]
      have : R (Function.invFun R (R x)) = R x := by
        have : ∃ y, R y = R x := ⟨x, rfl⟩
        apply Function.invFun_eq this
      apply hR_bijective.1
      exact this
    · ext x
      simp only [id_eq, comp_apply]
      have : ∃ y, R y = x := hR_bijective.2 x
      apply Function.invFun_eq this
  -- Apply $R^[n] = R^[m]$, consider the inverse operation.
  have h_diff : R^[m - n] = id := by
    have h_m_eq_n_plus : R^[m] = R^[n + (m - n)] := by
      have : n ≤ m := Nat.le_of_lt hnm
      rw [Nat.add_sub_of_le this]
    have h_iterate_add : R^[n + (m - n)] = R^[n] ∘ R^[m - n] := by
      rw [iterate_add]
    have h_m_eq_compose : R^[m] = R^[n] ∘ R^[m - n] := by
      rw [h_m_eq_n_plus, h_iterate_add]
    have h_n_eq_m : R^[n] = R^[m] := hnm_eq
    have h_n_eq_compose : R^[n] = R^[n] ∘ R^[m - n] := by
      rw [← h_m_eq_compose, <-h_n_eq_m]
    have h_n_id : R^[n] ∘ id = R^[n] := by
      simp
    have h_compose_eq_id : R^[n] ∘ R^[m - n] = R^[n] ∘ id := by
      rw [← h_n_eq_compose, h_n_id]
    ext x
    have h_inj_n : Function.Injective (R^[n]) := Function.Injective.iterate hR n
    have : (R^[n] ∘ R^[m - n]) x = (R^[n] ∘ id) x := by
      rw [h_compose_eq_id]
    simp only [comp_apply] at this
    apply h_inj_n
    exact this
  -- Conclude that there exists n such that $R^[n] = id$.
  use m - n