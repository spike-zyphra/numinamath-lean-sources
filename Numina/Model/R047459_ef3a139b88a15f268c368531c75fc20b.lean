import Mathlib

theorem algebra_14516 : {c : ℝ | ∃ a b x y : ℝ, 2 * x - y = a ∧ 3 * y - 6 * x = b ∧ b ≠ 0 ∧ c = a / b} = {-1/ 3} := by 
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, proving if $c \in \{ \cdots \}$ then $c = -1/3$.
    rintro ⟨a, b, x, y, h1, h2, hb, hc⟩
    have eq1 : b = -3 * a := by
      linarith
    have h3 : a ≠ 0 := by
      by_contra h
      rw [h] at eq1
      have h3 : b = 0 := by
        linarith
      contradiction
    have h3' : a / b = -1 / 3 := by
      rw [eq1]
      field_simp [(show a ≠ 0 by assumption)]
      <;> linarith
    rw [hc]
    linarith
  · -- Second, proving if $c = -1/3$ then $c \in \{ \cdots \}$.
    intro hc
    rw [hc]
    use 1, -3, (0 : ℝ), (-1 : ℝ)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num