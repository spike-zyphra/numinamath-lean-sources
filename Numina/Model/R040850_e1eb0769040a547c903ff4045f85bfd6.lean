import Mathlib


theorem number_theory_7301 (P : ℕ → Prop) (hP : ∀ n, 2 ≤ n → P n → P (n - 1)) (hP' : {n | P n}.Infinite) : ∀ n≥ 1, P n := by
  intro n hn
  have h4 : ∀ (k : ℕ), (∃ m ∈ {n | P n}, m > k) := by
    rw [Set.infinite_iff_exists_gt] at hP'
    intro k
    specialize hP' k
    simpa using hP' 
  have h3 := h4 n
  rcases h3 with ⟨m, hm1, hm2⟩
  have hm4 : P m := by
    have h10 : m ∈ {n | P n} := hm1
    simp at h10 ⊢
    exact h10
  have hm5 : m ≥ n + 1 := by omega
  have h3 : ∀ (k : ℕ), k ≤ m - (n) → P (m - k) := by
    intro k hk
    induction k with
    | zero =>
      simp
      all_goals assumption
    | succ i ih =>
      have h7 : m - (i + 1) = (m - i) - 1 := by
        omega
      rw [h7]
      have h8 : 2 ≤ (m - i : ℕ) := by
        omega
      have h9 : P (m - i : ℕ) := ih (by omega)
      specialize hP ((m - i : ℕ)) (by omega) h9
      simpa using hP
  -- Now, to show P n, we set k = m - n
  have hm3 : P n := by
    have h13 : m - (m - n) = n := by
      omega
    have h14 : m - (m - n) = n := h13
    have h15 := h3 (m - n) (by omega)
    rw [h14] at h15
    exact h15
  exact hm3