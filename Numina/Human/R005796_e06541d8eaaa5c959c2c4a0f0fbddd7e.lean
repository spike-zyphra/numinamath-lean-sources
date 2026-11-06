import Mathlib

open Real Set

/- Let $d$ be a real number such that every non-degenerate quadrilateral has at least two interior angles with measure less than $d$ degrees. What is the minimum possible value for $d$ ?
Answer: 120. -/
theorem geometry_609963 :
    IsLeast {d : ℝ | ∀ A B C D : ℝ, A ∈ Ioo 0 180 → B ∈ Ioo 0 180 → C ∈ Ioo 0 180 → D ∈ Ioo 0 180 →
    A + B + C + D = 360 → A ≤ B → B ≤ C → C ≤ D → A < d ∧ B < d} 120 := by
  -- The sum of the internal angles of a quadrilateral triangle is $360^{\circ}$.
  -- To find the minimum $d$, we note the limiting case where three of the angles have measure $d$ and the remaining angle has measure approaching zero.
  -- Hence, $d \geq 360^{\circ} / 3=120$.
  -- It is not difficult to see that for any $0<\alpha<120$, a quadrilateral of which three angles have measure $\alpha$ degrees and fourth angle has measure ( $360-3 \alpha$ ) degrees can be constructed.
  constructor
  · -- We show that `d = 120` satisfies the assumption.
    simp only [mem_Ioo, and_imp, mem_setOf_eq]
    intro A B C D hA hA' hB hB' hC hC' hD hD' h hAB hBC hCD
    by_contra! hc
    obtain hc' | hc' : A < 120 ∨ 120 ≤ A := by exact lt_or_le A 120
    · linarith [hc hc']
    · linarith
  · -- We show that `d` is at least `120`.
    simp only [mem_Ioo, and_imp]
    intro d h
    apply le_of_forall_pos_le_add
    intro ε hε
    rw [mem_setOf_eq] at h
    by_contra! hd
    let A := min ε 10
    let B : ℝ := 120 - A
    let C : ℝ := 120
    let D : ℝ := 120
    have hA : 0 < A := by
      simpa [A]
    have hA'' : A ≤ 10 := by
      simp [A]
    have hB : 0 < B := by
      simp only [sub_pos, inf_lt_iff, B, A]
      right
      linarith
    have hB' : B < 180 := by
      dsimp [B]
      linarith
    have hABCD : A + B + C + D = 360 := by
      dsimp [B, C, D]
      linarith
    have hAB : A ≤ B := by
      have : 10 ≤ B := by
        dsimp [B]
        linarith
      linarith

    have hABd := h A B C D hA (by linarith) hB hB' (by exact Nat.ofNat_pos') (by dsimp [C]; linarith)
      (by simp) (by simp [D]; linarith) hABCD hAB (by dsimp [B, C]; linarith) (by simp [B, C])

    obtain hc | hc : ε < 10 ∨ 10 ≤ ε := by exact lt_or_le ε 10
    · have hA'' : A = ε := by
        dsimp [A]
        rw [inf_eq_left]
        linarith
      have := hABd.2
      simp only [hA'', B] at this
      linarith
    · have : A = 10 := by
        rw [min_eq_right_iff]
        exact hc
      have : B = 110 := by
        dsimp [B]
        linarith
      have : d < 110 := by linarith
      linarith
