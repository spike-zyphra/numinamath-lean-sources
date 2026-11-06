import Mathlib

/-
Let $m$ and $n$ be positive integers, and let $y$ be a positive real number. Prove that
\[ \sum_{i=1}^n \min\left(\left\lfloor \frac{y}{i} \right\rfloor, m \right) = \sum_{i=1}^m \min\left(\left\lfloor \frac{y}{i} \right\rfloor, n \right). \]
 -/
theorem number_theory_641617 (m n : ℕ) (y : ℝ) (hm : 0 < m) (hn : 0 < n) (hy : 0 < y) :
    ∑ i in Finset.Icc 1 n, ⌊y / i⌋₊ ⊓ m = ∑ i in Finset.Icc 1 m, ⌊y / i⌋₊ ⊓ n := by
  have sum_eq_mul_le_y_card (m n : ℕ) : ∑ i in Finset.Icc 1 m, ⌊y / i⌋₊ ⊓ n =
      ((Finset.Icc 1 m ×ˢ Finset.Icc 1 n).filter fun (i, j) => i * j ≤ y).card := by
    let t (i : ℕ ) := ((Finset.Icc 1 n).filter fun (j : ℕ) => i * j ≤ y).map ⟨(i, .), by simp [Function.Injective]⟩
    have pairwiseDisjoint : (Finset.Icc 1 m : Set ℕ).PairwiseDisjoint t := by
      intro i₁ i₁_in i₂ i₂_in i_ne_j
      refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
      ext ⟨i, j⟩
      simp
      intro i_j_in_t_i₁ i_j_in_t_i₂
      simp [t] at i_j_in_t_i₁ i_j_in_t_i₂
      --rcases i_j_in_t_i₁ with ⟨⟨⟨j_ge, j_le⟩, i₁_j_le_y⟩, i₁_eq_i⟩ -- only `i₁ = i` needed
      rcases i_j_in_t_i₁ with ⟨_, rfl⟩
      rcases i_j_in_t_i₂ with ⟨_, rfl⟩
      contradiction
    have : (Finset.Icc 1 m ×ˢ Finset.Icc 1 n).filter fun (i, j) => i * j ≤ y =
        (Finset.Icc 1 m).disjiUnion t pairwiseDisjoint := by
      ext ⟨i, j⟩
      simp [t]
      exact and_assoc --tauto
    rw [this]
    rw [Finset.card_disjiUnion]
    /- This approach throws away `i ∈ Finset.Icc 1 m` which is needed.
    congr
    ext i
     -/
    apply Finset.sum_congr rfl
    intro i i_in
    unfold t
    simp only [Finset.card_map]
    have : ((Finset.Icc 1 n).filter fun (j : ℕ) => i * j ≤ y) = Finset.Icc 1 (⌊y / i⌋₊ ⊓ n) := by
      ext j
      simp
      have : i * j ≤ y ↔ j ≤ ⌊y / i⌋₊ := by
        have i_pos : i > 0 := by
          simp at i_in
          linarith
        rify at i_pos
        constructor
        . intro i_j_le_y
          have : j ≤ y / i := by
            exact (le_div_iff₀' i_pos).mpr i_j_le_y
          exact Nat.le_floor this
        . intro j_le_y_div_i_floor
          have : j ≤ y / i := by
            have : ⌊y / i⌋₊ ≤ y / i := by
              set x := y / i
              have : x ≥ 0 := by
                suffices x > 0 by
                  linarith
                unfold x
                exact div_pos hy i_pos
              exact Nat.floor_le this
            rify at j_le_y_div_i_floor
            linarith
          exact (le_mul_inv_iff₀' i_pos).mp this
      rw [this]
      tauto
    rw [this]
    set n' := ⌊y / ↑i⌋₊ ⊓ n
    rw [Nat.card_Icc]
    simp
  repeat rw [sum_eq_mul_le_y_card]
  set s := (Finset.Icc 1 n ×ˢ Finset.Icc 1 m).filter fun (i, j) => i * j ≤ y
  set t := (Finset.Icc 1 m ×ˢ Finset.Icc 1 n).filter fun (i, j) => i * j ≤ y
  have : t = s.map ⟨fun (i, j) => (j, i), by simp [Function.Injective]⟩ := by
    ext ⟨i, j⟩
    simp [s, t, -Finset.mem_Icc]
    let P₁ i := i ∈ Finset.Icc 1 m
    let P₂ j := j ∈ Finset.Icc 1 n
    let P₃ i j := i * j ≤ y
    show (P₁ i ∧ P₂ j) ∧ P₃ i j ↔ ∃ j' i', ((P₂ j' ∧ P₁ i') ∧ P₃ j' i') ∧ (i' = i ∧ j' = j)
    constructor
    . simp
      intro p₁_i p₂_j p₃_i_j
      use j, i
      simp [p₁_i, p₂_j]
      --unfold P₃ at p₃_i_j ⊢
      linarith
    . simp
      rintro j i p₂_j p₁_i p₃_j_i rfl rfl
      simp [p₁_i, p₂_j]
      linarith
  rw [this]
  simp
