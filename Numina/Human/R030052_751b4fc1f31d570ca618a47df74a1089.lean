import Mathlib

open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators

/- 122. a) Prove that if a sequence has a limit, then it is bounded.

b) Is the converse statement true? -/
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
  -- The sequence given by $ a_n = (-1)^n $ is bounded but does not converge
  use (fun n : ℕ => (-1) ^ n)
  constructor
  -- It is bounded in absolute value by 1
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    use 1
    simp [Set.range_subset_iff]
  -- It does not converge
  · by_contra h
    -- If it did, let $ L $ be its limit
    obtain ⟨L, hL⟩ := h
    have := hL (Metric.ball_mem_nhds L (ε := 1/2) (by linarith))
    simp [dist] at this
    -- We can find $ n $ such that $ a_k $ is less than $ 1/2 $ away from $ L $ for all $ k \geq n $
    obtain ⟨n, hn⟩ := this
    -- But this is a contradiction, because the sequence alternates between $ -1 $ and $ 1 $
    have heven := hn (2 * n) (by linarith)
    have hodd := hn (2 * n + 1) (by linarith)
    simp [abs_lt] at heven
    simp [pow_add, abs_lt] at hodd
    linarith