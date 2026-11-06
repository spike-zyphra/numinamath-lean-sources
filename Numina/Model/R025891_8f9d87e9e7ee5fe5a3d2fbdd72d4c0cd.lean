import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem algebra_165789 (x : ℕ → ℝ)
  (hx0 : x 0 = 1)
  (hxn : ∀ n, x (n + 1) = x n - (x n)^2 / 2023) :
  ∃ L, Tendsto x atTop (𝓝 L) ∧ L = 0 := by
  have h1 : ∀ n, 0 ≤ x n := by
    intro n
    induction n with
    | zero =>
      rw [hx0]
      norm_num
    | succ n ih =>
      have h3 : x (n + 1) = x n - (x n) ^ 2 / 2023 := hxn n
      have h4 : x n ≤ 2023 := by
        have h2 : ∀ n, x n ≤ 2023 := by
          intro n
          induction n with
          | zero =>
            rw [hx0]
            norm_num
          | succ n ih2 =>
            have h3 : x (n + 1) = x n - (x n) ^ 2 / 2023 := hxn n
            rw [h3]
            have h5 : x n ≤ 2023 := ih2
            have h7 : (x n) ^ 2 - 2023 * (x n) + (2023 : ℝ) ^ 2 ≥ 0 := by
              nlinarith [sq_nonneg ((x n) - 2023 / 2)]
            have h12 : 2023 * (x n) - (x n) ^ 2 ≤ (2023 : ℝ) ^ 2 := by
              nlinarith
            have h13 : (x n : ℝ) - (x n) ^ 2 / 2023 ≤ (2023 : ℝ) := by
              have h14 : 2023 * (x n) - (x n) ^ 2 ≤ (2023 : ℝ) ^ 2 := h12
              have h15 : (x n : ℝ) - (x n) ^ 2 / 2023 = (2023 * (x n) - (x n) ^ 2) / (2023 : ℝ) := by
                field_simp
                <;> linarith
              rw [h15]
              have h16 : (2023 * (x n) - (x n) ^ 2) / (2023 : ℝ) ≤ (2023 : ℝ) := by
                apply (div_le_iff₀ (by norm_num)).mpr
                linarith
              linarith
            linarith
        specialize h2 n
        linarith
      rw [h3]
      have h10 : (x n : ℝ) - (x n) ^ 2 / 2023 ≥ 0 := by
        have h11 : 0 ≤ x n := ih
        have h12 : x n ≤ 2023 := h4
        have h14 : (x n) ^ 2 ≤ (x n) * 2023 := by
          nlinarith [sq_nonneg (x n - 2023)]
        have h16 : (x n) ^ 2 / 2023 ≤ (x n : ℝ) := by
          have h17 : (x n) ^ 2 ≤ (x n) * 2023 := h14
          have h18 : (x n) ^ 2 / 2023 ≤ (x n : ℝ) := by
            apply (div_le_iff₀ (by norm_num)).mpr
            nlinarith
          linarith
        linarith
      linarith
  have h2 : ∀ n, x (n + 1) ≤ x n := by
    intro n
    have h3 : x (n + 1) = x n - (x n) ^ 2 / 2023 := hxn n
    rw [h3]
    have h4 : (x n) ^ 2 ≥ 0 := sq_nonneg (x n)
    have h5 : (x n) ^ 2 / 2023 ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals norm_num
    have h6 : (x n : ℝ) - (x n) ^ 2 / 2023 ≤ (x n : ℝ) := by
      linarith
    linarith
  use (0 : ℝ)
  constructor
  · -- Show that x tends to 0
    have h47 : Tendsto x atTop (𝓝 (0 : ℝ)) := by
      have h48 : Antitone x := by
        intro n m hnm
        have h37 : x m ≤ x n := by
          have h38 : ∀ (k : ℕ), x (n + k) ≤ x n := by
            intro k
            induction k with
            | zero => 
              simp
            | succ k ih =>
              have h13 : x (n + k + 1) ≤ x (n + k) := by
                specialize h2 (n + k)
                simpa using h2
              have h14 : x (n + k) ≤ x n := ih
              show x (n + (k + 1)) ≤ x n
              calc
                x (n + (k + 1)) = x (n + k + 1) := by ring
                _ ≤ x (n + k) := h13
                _ ≤ x n := h14
          have h12 : n ≤ m := by linarith
          have h13 : ∃ k, m = n + k := by
            refine' ⟨m - n, by omega⟩
          rcases h13 with ⟨k, hk⟩
          have h14 : x m ≤ x n := by
            rw [show m = n + k by linarith [hk]]
            apply h38 k
          linarith
        linarith
      have h38 : BddBelow (Set.range x) := by
        use 0
        intro y
        rintro ⟨n, hn⟩
        rw [← hn]
        exact h1 n
      have h39 : ∃ L, Tendsto x atTop (𝓝 L) := by
        exact (Real.tendsto_of_bddBelow_antitone h38 h48)
      rcases h39 with ⟨L, h39⟩
      have h47 : L = 0 := by
        have h48 : L ^ 2 = 0 := by
          have h51 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 L) := by
            have h110 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 L) := by
              have h111 : Tendsto (fun n : ℕ => x n) atTop (𝓝 L) := h39
              have h112 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 L) := by
                simpa using h111.comp (tendsto_add_atTop_nat 1)
              exact h112
            exact h110
          have h52 : Tendsto (fun n : ℕ => x n - (x n) ^ 2 / 2023) atTop (𝓝 (L - L ^ 2 / 2023)) := by
            have h120 : Tendsto (fun n : ℕ => x n) atTop (𝓝 L) := h39
            have h121 : Tendsto (fun n : ℕ => (x n) ^ 2) atTop (𝓝 (L ^ 2)) := by
              apply Tendsto.pow
              exact h39
            have h122 : Tendsto (fun n : ℕ => (x n) ^ 2 / 2023) atTop (𝓝 (L ^ 2 / 2023)) := by
              apply Tendsto.div_const
              exact h121
            have h123 : Tendsto (fun n : ℕ => x n - (x n) ^ 2 / 2023) atTop (𝓝 (L - L ^ 2 / 2023)) := by
              apply Tendsto.sub
              exact h120
              exact h122
            exact h123
          have h53 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 (L - L ^ 2 / 2023)) := by
            have h130 : ∀ n, x (n + 1) = x n - (x n) ^ 2 / 2023 := by
              intro n
              specialize hxn n
              simpa using hxn
            have h131 : (fun n : ℕ => x (n + 1)) = (fun n : ℕ => x n - (x n) ^ 2 / 2023) := by
              funext n
              exact h130 n
            rw [h131]
            exact h52
          have h54 : L = L - L ^ 2 / 2023 := by
            have h140 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 L) := h51
            have h141 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 (L - L ^ 2 / 2023)) := h53
            have h142 : (L : ℝ) = (L - L ^ 2 / 2023 : ℝ) := by
              exact tendsto_nhds_unique h140 h141
            linarith
          nlinarith
        have h56 : L = 0 := by
          nlinarith
        exact h56
      simp [h47] at h39 ⊢
      all_goals
      try tauto
    exact h47
  · -- Show that L = 0
    rfl