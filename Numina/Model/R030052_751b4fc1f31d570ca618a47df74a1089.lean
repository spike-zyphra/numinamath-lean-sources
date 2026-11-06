import Mathlib

open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators

theorem calculus_116756_1
  (a : ℕ → ℝ)
  (h : ∃ L, Tendsto a atTop (𝓝 L)) :
  Bornology.IsBounded (Set.range a) := by
  -- Let $ L $ be the limit of $ a $
  obtain ⟨L, hL⟩ := h
  -- Find $ n $ such that $ a_n $ is less than 1 away from $ L $
  have := hL (Metric.ball_mem_nhds L one_pos)
  simp at this
  obtain ⟨n, hn⟩ := this
  dsimp [dist] at hn
  -- Find a bound for the absolute value of the terms before $ a_n $ in the sequence
  have : ∃ B, ∀ k < n, |a k| ≤ B := by
    by_cases h0 : n = 0
    · use 0; simp [h0]
    · have : ((range n).image (abs ∘ a)).Nonempty
        := Finset.Nonempty.image (Finset.nonempty_range_iff.mpr h0) _
      use ((range n).image (abs ∘ a)).max' this
      intro k hk
      apply Finset.le_max'
      simp
      use k
  obtain ⟨B, hB⟩ := this
  -- We show that the difference between any two terms in the sequence is bounded by $ 2(B + 2) $
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use max (|L| + 1) B
  rw [Set.range_subset_iff]
  intro x
  simp
  by_cases hx : n ≤ x
  · apply Or.inl
    calc |a x| = |(a x - L) + L| := by ring_nf
    _ ≤ |a x - L| + |L| := abs_add_le _ _
    _ ≤ 1 + |L| := add_le_add (le_of_lt (hn x hx)) (le_refl _)
    _ = |L| + 1 := add_comm _ _
  · apply Or.inr
    rw [not_le] at hx
    exact hB x hx

theorem calculus_116756_2 :
  ∃ a : ℕ → ℝ, Bornology.IsBounded (Set.range a) ∧
    ¬ ∃ L, Tendsto a atTop (𝓝 L) := by
  use fun (n : ℕ) => (-1 : ℝ) ^ n
  constructor
  · -- Show that `range a` is bounded.
    apply Metric.isBounded_iff_subset_closedBall 0 |>.mpr
    use 1
    intro x hx
    simp at hx ⊢
    rcases hx with ⟨n, rfl⟩
    have h1 : |(-1 : ℝ) ^ n| = 1 := by
      have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
        have h1 : ∀ n : ℕ, (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
          intro n
          induction n with
          | zero => 
            norm_num
          | succ n ih =>
            simp [pow_succ] at ih ⊢
            cases ih with
            | inl h => 
              simp [h]
              all_goals linarith
            | inr h => 
              simp [h]
              all_goals linarith
        apply h1 n
      cases h2 with
      | inl h => 
        rw [h]
        all_goals norm_num
      | inr h => 
        rw [h]
        all_goals norm_num
    simpa [h1] using abs_le.mpr h1
  · -- Show that `a` does not converges.
    intro h
    rcases h with ⟨L, hL⟩
    -- Let $\epsilon = 1/2$. Find $N$ such that for $n \geq N$, $|a_n - L| < 1/2$
    have h1 := hL (Metric.ball_mem_nhds L (by norm_num : (1 / 2 : ℝ) > 0))
    simp at h1
    rcases h1 with ⟨N, hN⟩
    have h2 := hN (2 * N)
    have h3 := hN (2 * N + 1)
    have h4 : ((-1 : ℝ) : ℝ) ^ (2 * N) = 1 := by
      have h1 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) = 1 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          <;> linarith [ih]
      specialize h1 N
      simpa using h1
    have h5 : ((-1 : ℝ) : ℝ) ^ (2 * N + 1) = -1 := by
      have h2 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) = -1 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          <;> linarith [ih]
      specialize h2 N
      simpa using h2
    rw [h4] at h2
    rw [h5] at h3
    -- Show that $L$ contradicts.
    have h6 : N ≤ 2 * N := by omega
    have h7 : N ≤ 2 * N + 1 := by omega
    have h8 : |1 - L| < (1 / 2 : ℝ) := by
      specialize h2 h6
      simpa using h2
    have h9 : |-1 - L| < (1 / 2 : ℝ) := by
      specialize h3 h7
      simpa using h3
    cases' abs_lt.mp h8 with h10 h11
    cases' abs_lt.mp h9 with h12 h13
    all_goals 
      linarith