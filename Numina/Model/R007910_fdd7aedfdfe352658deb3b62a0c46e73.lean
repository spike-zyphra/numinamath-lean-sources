import Mathlib

theorem algebra_10831 : {z : ℝ| z^2 - 40 * z + 340 ≤ 4} = Set.Icc 12 28 := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Forward direction: if $z^2 - 40z + 340 \leq 4$, then $12 \leq z \land z \leq 28$
    intro h
    constructor
    · -- Proof that 12 ≤ z
      nlinarith [sq_nonneg (z - 12), sq_nonneg (z - 28)]
    · -- Proof that z ≤ 28
      nlinarith [sq_nonneg (z - 12), sq_nonneg (z - 28)]
  · -- Backward direction: if $12 \leq z \leq 28$, then $z^2 - 40 z + 340 \leq 4$
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (z - 12), sq_nonneg (z - 28)]