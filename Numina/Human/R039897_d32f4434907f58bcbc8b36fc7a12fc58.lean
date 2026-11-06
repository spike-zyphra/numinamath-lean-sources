import Mathlib

open Topology Filter

/- 25.11. Prove that any bounded sequence has at least one limit point (Bolzano-Weierstrass). -/
theorem calculus_228123 (a : ℕ → ℝ) (h : ∃ B, ∀ n, |a n| ≤ B) :
    ∃ (l : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 l) := by
  -- express bounded ness as belonging to a closed interval
  obtain ⟨b, hb⟩ := h
  replace hb (n : ℕ) : a n ∈ Set.Icc (-b) b := by
    simp
    rw [← abs_le]
    exact hb n
  -- a closed interval is bounded as it is a closed ball
  have hb' : Bornology.IsBounded (Set.Icc (-b) b) := by
    rw [Real.Icc_eq_closedBall]
    exact Metric.isBounded_closedBall
  -- so we can use general bolzano weirstress
  obtain ⟨l, hl, hl'⟩  := tendsto_subseq_of_bounded hb' hb
  use l