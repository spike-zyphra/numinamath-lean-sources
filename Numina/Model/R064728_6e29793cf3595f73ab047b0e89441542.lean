import Mathlib

open Set Real

/- Given $a\geqslant -2$, and $A=\left\{ x\left| -2\leqslant x\leqslant a \right. \right\}$, $B=\left\{ y\left| y=2x+3,x\in A \right. \right\}$, $C=\left\{ t\left| t={{x}^{2}},x\in A \right. \right\}$, if $C\subseteq B$, then the range of values for $a$ is ___          ___. -/
theorem algebra_10372 {a : ℝ} (ha : -2 ≤ a) (B C : Set ℝ)
    (hB : B = {x | ∃ t ∈ Icc (-2) a, x = 2 * t + 3}) (hC : C = {x | ∃ t ∈ Icc (-2) a, x = t ^ 2})
    (h : C ⊆ B) :
    1 / 2 ≤ a ∧ a ≤ 3 := by

  have h1 : 1 / 2 ≤ a := by
    by_contra h1
    push_neg at h1
    have h2 : (4 : ℝ) ∈ C := by
      rw [hC]
      use -2
      constructor
      · -- Show that -2 ∈ Icc (-2) a
        simp [Icc]
        all_goals linarith
      · -- Compute (-2)^2 = 4
        norm_num

    have h3 : (4 : ℝ) ∈ B := h h2
    rw [hB] at h3
    rcases h3 with ⟨t, ht, ht_eq⟩
    simp [Icc] at ht
    have ht1 : -2 ≤ t := ht.1
    have ht2 : t ≤ a := ht.2
    nlinarith [ht_eq, h1, ht2]

  have h2 : a ≤ 3 := by
    by_contra h2
    push_neg at h2
    have h3 : (a^2 : ℝ) ∈ C := by
      rw [hC]
      use a
      constructor
      · -- Show a ∈ Icc (-2) a
        simp [Icc]
        all_goals linarith
      · -- Compute a^2 = a^2
        all_goals nlinarith

    have h4 : (a^2 : ℝ) ∈ B := h h3
    rw [hB] at h4
    rcases h4 with ⟨t, ht, ht_eq⟩
    simp [Icc] at ht
    have ht1 : -2 ≤ t := ht.1
    have ht2 : t ≤ a := ht.2
    nlinarith [ht_eq, ht2, h2]

  constructor
  · linarith [h1]
  · linarith [h2]