import Mathlib

theorem algebra_13783 : {c : ℝ | c / 3 ≤ 2 + c ∧ 2 + c < -2 * (1 + c)} = Set.Ico (-3) (-4 / 3) := by 
  ext c 
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume $\frac{c}{3} \le 2 + c \land 2 + c < -2(1 + c)$, prove $c \in [-3, -\frac{4}{3})$
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that $-3 \le c$
      linarith
    · -- Show that $c < -4 / 3$
      linarith 
  · -- Assume $c \in [-3, -\frac{4}{3})$, prove $\frac{c}{3} \le 2 + c \land 2 + c < -2(1 + c)$
    rintro ⟨h1, h2⟩ 
    constructor 
    · -- Show that $\frac{c}{3} \le 2 + c$
      linarith 
    · -- Show that $2 + c < -2 * (1 + c)$
      linarith