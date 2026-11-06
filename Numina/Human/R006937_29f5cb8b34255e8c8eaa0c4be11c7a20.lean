import Mathlib

open Finset

/-
For how many positive integers $n \leq 1000$ does the equation in real numbers $x^{\lfloor x\rfloor}=n$
have a positive solution for $x$ ?
(For a real number $x,\lfloor x\rfloor$ denotes the largest integer that is not greater than $x$.)
-/
theorem number_theory_610239 :
    let S := {n : ℕ | n > 0 ∧ n ≤ 1000 ∧ ∃ (x : ℝ) (hx : x > 0), x ^ ⌊x⌋ = n}
    S.encard = 412 := by
  -- Denote $S$ the set of positive integers $n \leq 1000$ such that
  -- there exists a positive real number $x$ such that $x^{⌊x⌋} = n$.
  intro S


  -- Let $A_k$ be the set of positive integers $n \leq 1000$ such that
  -- there exists a positive real number $x$ such that $\lfloor x \rfloor = k$ and $x^k = n$.
  let A (k : ℕ) := {n : ℕ | n > 0 ∧ n ≤ 1000 ∧ ∃ (x : ℝ) (hx : x > 0) (hx1 : x ≥ k) (hx2 : x < k + 1), x ^ k = n}

  -- Set $S$ is the union of sets $A_k$ for $k = 0, 1, 2, 3, 4$.
  have h1 : S = A 0 ∪ A 1 ∪ A 2 ∪ A 3 ∪ A 4 := by
    ext n
    dsimp [S, A]
    constructor
    . intro ⟨h1, h2, x, hx, h3⟩
      simp only [Set.mem_union]
      have g1 : x < 5 := by
        by_contra! g1
        have f1 : 5 ≤ ⌊x⌋ := by exact Int.le_floor.mpr g1
        have f2 := calc
          (5 : ℝ) ^ (5 : ℕ) ≤ x ^ (5 : ℕ) := by
            refine pow_le_pow_left₀ ?_ g1 5
            norm_num
          _ ≤ x ^ ⌊x⌋ := by
            refine (zpow_le_zpow_iff_right₀ ?_).mpr f1
            linarith
          _ ≤ n := by linarith
        norm_cast at f2
        omega
      have g2 : ⌊x⌋ < 5 := by exact Int.floor_lt.mpr g1
      have g3 : ⌊x⌋ ≥ 0 := by exact Int.floor_nonneg.mpr (by linarith)
      have g4 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 ∨ ⌊x⌋ = 4 := by omega
      obtain g4 | g4 | g4 | g4 | g4 := g4
      . left; left; left; left
        have ⟨g5, g6⟩ := Int.floor_eq_iff.mp g4
        use h1, h2, x, hx, g5, g6
        simpa [g4] using h3
      . left; left; left; right
        have ⟨g5, g6⟩ := Int.floor_eq_iff.mp g4
        use h1, h2, x, hx, g5, g6
        simpa [g4] using h3
      . left; left; right
        have ⟨g5, g6⟩ := Int.floor_eq_iff.mp g4
        use h1, h2, x, hx, g5, g6
        simpa [g4] using h3
      . left; right
        have ⟨g5, g6⟩ := Int.floor_eq_iff.mp g4
        use h1, h2, x, hx, g5, g6
        simpa [g4] using h3
      . right
        have ⟨g5, g6⟩ := Int.floor_eq_iff.mp g4
        use h1, h2, x, hx, g5, g6
        simpa [g4] using h3
    . simp only [Set.mem_union]
      intro h1
      obtain (((h1 | h1) | h1) | h1) | h1 := h1
      all_goals
        obtain ⟨h2, h3, x, hx, hx1, hx2, h1⟩ := h1
        use h2, h3, x, hx
        have g1 := Int.floor_eq_iff.mpr ⟨hx1, hx2⟩
        simpa [g1] using h1

  -- $A_0$ is the singleton set $\{1\}$ so it is included in $A_1$.
  have h2 : A 0 = {1} := by
    ext n
    constructor
    . intro ⟨hn, hn2, x, hx, hx1, hx2, g1⟩
      suffices n = 1 from by simpa
      rify
      simpa using g1.symm
    . intro g1
      replace g1 : n = 1 := by simpa using g1
      subst g1
      simp [A]
      use 1 / 2
      norm_num

  have h3 : A 0 ⊆ A 1 := by
    rw [h2]
    simp [A]
    use 1
    norm_num

  -- Therefore the set $S$ can be written as the union of the sets $A_k$ for $k = 1, 2, 3, 4$.
  replace h1 : S = A 1 ∪ A 2 ∪ A 3 ∪ A 4 := by
    rw [h1]
    congr 3
    exact Set.union_eq_self_of_subset_left h3

  -- $A_k$ is the set $[k^k, (k+1)^k)$ for $k = 1, 2, 3, 4$.
  have h4 k (hk : k ≥ 1) (hk2 : k ≤ 4) : A k = Set.Ico (k ^ k) ((k + 1) ^ k) := by
    ext n
    constructor
    . intro ⟨hn, hn2, x, hx, hx1, hx2, g1⟩
      constructor
      . rify
        rw [←g1]
        exact pow_le_pow_left₀ (by linarith) hx1 k
      . rify
        rw [←g1]
        exact pow_lt_pow_left₀ hx2 (by linarith) (by linarith)
    . intro ⟨g1, g2⟩
      have g3 : n > 0 := calc
          _ ≥ _ := g1
          _ ≥ 1 := Nat.one_le_pow k k hk
          _ > _ := by norm_num
      use g3
      use calc
          n ≤ (k + 1) ^ k := by linarith
          _ ≤ (k + 1) ^ 4 := by exact (Nat.pow_le_pow_iff_right (by omega)).mpr hk2
          _ ≤ 5 ^ 4 := by exact Int.pow_le_pow_of_le_left (by omega) 4
          _ ≤ _ := by norm_num
      use (n : ℝ) ^ (1 / k : ℝ)
      use by exact Real.rpow_pos_of_pos (by norm_cast) (1 / k : ℝ)
      use by
        refine (Real.rpow_inv_le_iff_of_pos ?_ ?_ ?_).mp ?_
        . simp
        . simp
        . field_simp; omega
        . field_simp; norm_cast
      use by
        refine (Real.lt_rpow_inv_iff_of_pos ?_ ?_ ?_).mp ?_
        . simp
        . norm_cast; omega
        . field_simp; omega
        . field_simp; norm_cast
      rw [←Real.rpow_mul_natCast (by linarith)]
      field_simp

  -- As the $A_k$'s are disjoint, we can obtain the cardinality of $S$
  -- by summing the cardinalities of the $A_k$'s.
  have h5 : S.encard = (A 1).encard + (A 2).encard + (A 3).encard + (A 4).encard := by
    rw [h1]
    rw [Set.encard_union_eq]
    rw [Set.encard_union_eq]
    rw [Set.encard_union_eq]
    . intro s hs1 hs2 n hns
      specialize hs1 hns
      specialize hs2 hns
      rw [h4 1 (by omega) (by omega)] at hs1
      rw [h4 2 (by omega) (by omega)] at hs2
      simp [Set.Ico] at hs1 hs2
      omega
    . intro s hs1 hs2 n hns
      specialize hs1 hns
      specialize hs2 hns
      rw [h4 1 (by omega) (by omega)] at hs1
      rw [h4 2 (by omega) (by omega)] at hs1
      rw [h4 3 (by omega) (by omega)] at hs2
      simp [Set.Ico] at hs1 hs2
      omega
    . intro s hs1 hs2 n hns
      specialize hs1 hns
      specialize hs2 hns
      rw [h4 1 (by omega) (by omega)] at hs1
      rw [h4 2 (by omega) (by omega)] at hs1
      rw [h4 3 (by omega) (by omega)] at hs1
      rw [h4 4 (by omega) (by omega)] at hs2
      simp [Set.Ico] at hs1 hs2
      omega

  -- $A_1$ is the set $[1, 2)$ so it has cardinality $1$.
  -- $A_2$ is the set $[4, 9)$ so it has cardinality $5$.
  -- $A_3$ is the set $[27, 64)$ so it has cardinality $37$.
  -- $A_4$ is the set $[256, 625)$ so it has cardinality $369$.
  -- Therefore $S$ has cardinality $1 + 5 + 37 + 369 = 412$.
  calc
    _ = _ := h5
    _ = 1 + 5 + 37 + 369 := by
      congr 3
      . rw [h4 1 (by omega) (by omega)]
        simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_Ico, Nat.card_Ico]
        norm_num
      . rw [h4 2 (by omega) (by omega)]
        simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_Ico, Nat.card_Ico]
        norm_num
      . rw [h4 3 (by omega) (by omega)]
        simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_Ico, Nat.card_Ico]
        norm_num
      . rw [h4 4 (by omega) (by omega)]
        simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_Ico, Nat.card_Ico]
        norm_num
    _ = 412 := by norm_num
