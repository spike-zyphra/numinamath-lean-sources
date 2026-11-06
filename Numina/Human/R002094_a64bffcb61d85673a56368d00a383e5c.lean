import Mathlib

-- Define the set L where the first player loses(The definition implies $L ∩ W = ∅$).
def is_losing (L W : Set ℕ) (n : ℕ) : Prop :=
  n ∈ L ↔ ∀ k : ℕ, k > 0 → n < k^2 ∨ n - k^2 ∈ W

-- Define the set W where the first player wins.
def is_winning (L W : Set ℕ) (n : ℕ) : Prop :=
  n ∈ W ↔ ∃ k : ℕ, k > 0 ∧ n ≥ k^2 ∧ n - k^2 ∈ L

/-Consider the following two person game. A number of pebbles are situated on the table. Two players make their moves alternately. A move consists of taking off the table $x$ pebbles where $x$ is the square of any positive integer. The player who is unable to make a move loses. Prove that there are infinitely many initial situations in which the second player can win no matter how his opponent plays.-/
theorem combinatorics_63800 {L W : Set ℕ}
    (hL : ∀ n, is_losing L W n)
    (hW : ∀ n, is_winning L W n)
    (hL0 : 0 ∈ L)
    (hLW_compl : L ∪ W = Set.univ) :
    ¬Finite L := by
  -- Proof by contradiction: Assume L is finite.
  intro hL_finite
  -- $L$ is non-empty (since $0 ∈ L$), so it has a maximum element.
  have hL_nonempty : L.Nonempty := by
    exact ⟨0, hL0⟩
  have hL_max : ∃ n : ℕ, n ∈ L ∧ ∀ m : ℕ, m ∈ L → m ≤ n := by
    have h_max := Set.Finite.exists_maximal_wrt id L hL_finite hL_nonempty
    rcases h_max with ⟨n, hn_s, h_maximal⟩
    refine ⟨n, hn_s, ?_⟩
    intro m hm
    have h_le_eq : id n ≤ id m → id n = id m := h_maximal m hm
    have h_m_le_n : m ≤ n := by
      cases Nat.le_total m n with
      | inl h_m_le_n => exact h_m_le_n
      | inr h_n_le_m =>
        have h_eq : n = m := h_le_eq (by simp [id]; exact h_n_le_m)
        rw [h_eq]
    exact h_m_le_n
  -- Take the maximum element $n$.
  rcases hL_max with ⟨n, hnL, h_max⟩
  -- Prove $n^2 + n + 1 ∈ L$.
  have hN_in_L : n^2 + n + 1 ∈ L := by
    have hL_N := hL (n^2 + n + 1)
    rw [is_losing] at hL_N
    apply hL_N.mpr
    intros k hk
    -- Prove $1$ in $W$.
    have h_1_in_W : 1 ∈ W := by
      have hW_1 := hW 1
      rw [is_winning] at hW_1
      apply hW_1.mpr
      exists 1
    -- Prove the maximum element $n > 0$ using $2 ∈ L$.
    have h_n_pos : n > 0 := by
      have h_2_in_L : 2 ∈ L := by
        have hL_2 := hL 2
        rw [is_losing] at hL_2
        apply hL_2.mpr
        intros k hk
        by_cases h_k_eq_1 : k = 1
        · right
          rw [h_k_eq_1]
          simp
          exact h_1_in_W
        · left
          have h_k_ge_2 : k ≥ 2 := by omega
          have h_k2_ge_4 : k^2 ≥ 4 := by nlinarith
          linarith
      have h_2_le_n : 2 ≤ n := h_max 2 h_2_in_L
      nlinarith
    by_cases h_k2_le_N : k^2 ≤ n^2 + n + 1
    · -- Case $1$: $k^2 ≤ n^2 + n + 1$.
      right
      have : k ≤ n := by nlinarith
      have h_k2_le_n2 : k^2 ≤ n^2 := by nlinarith
      have h_N_k2_ge_n_plus_1 : (n^2 + n + 1) - k^2 ≥ n + 1 := by omega
      -- Since $n$ is the maximum element of $L$, any number greater than n must be in $W$.
      have h_N_k2_in_W : (n^2 + n + 1) - k^2 ∈ W := by
        have h_N_k2_not_in_L : (n^2 + n + 1) - k^2 ∉ L := by
          intro h_in_L
          have h_le_n : (n^2 + n + 1) - k^2 ≤ n := h_max _ h_in_L
          linarith
        have h_diff_in_univ : (n^2 + n + 1) - k^2 ∈ Set.univ := Set.mem_univ _
        have : (n^2 + n + 1) - k^2 ∈ W := by
          rw [← hLW_compl] at h_diff_in_univ
          cases h_diff_in_univ with
          | inl h => contradiction
          | inr h => exact h
        exact this
      exact h_N_k2_in_W
    · --- Case $2$: $k^2 > n^2 + n + 1$.
      left
      exact lt_of_not_le h_k2_le_N
  -- Prove $n^2 + n + 1 > n$.
  have hN_gt_n : n^2 + n + 1 > n := by nlinarith
  -- $N ∈ L$ and $N > n$, contradicting maximality.
  have h_max_contr : n^2 + n + 1 ≤ n := h_max (n^2 + n + 1) hN_in_L
  linarith [hN_gt_n, h_max_contr]
