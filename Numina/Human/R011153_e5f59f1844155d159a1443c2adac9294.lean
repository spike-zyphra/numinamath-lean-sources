import Mathlib

-- we show a simple lemma for the condition of being a perfect square
lemma is_sq_eq_sq_of_pos (x: ℤ) (h: IsSquare x): ∃ r, 0 ≤ r ∧ x = r ^ 2 := by
  apply IsSquare.exists_sq at h
  obtain ⟨r, hr⟩ := h
  by_cases l: 0 ≤ r
  .
    use r
  .
    set t:= -r
    use t
    constructor
    .
      simp at l
      simp [t]
      linarith
    .
      simp [t]
      nlinarith

/-Let a b and c be distinct positive integers such that
a + b, b + c, c + a are all perfect squares.
Find the minimum possible value of
a + b + c.-/

theorem number_theory_623651: IsLeast {k: ℤ | ∃ a b c, k = a + b + c ∧ 0 < a ∧ a < b ∧ b < c ∧
  IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (b + c)} 55 := by

  constructor

  -- the forward direction
  .
    simp
    use 6
    use 19
    use 30
    norm_num
    native_decide


  -- the backward direction
  .
    intro k h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a, b, c, hk, ha, hb, hc, h1, h2, h3⟩ := h
    rw [hk]
    clear hk

    -- for convenience, we prove by contradiction
    by_contra! l
    apply is_sq_eq_sq_of_pos at h1
    obtain ⟨x, hx, h1⟩ := h1
    apply is_sq_eq_sq_of_pos at h2
    obtain ⟨y, hy, h2⟩ := h2
    apply is_sq_eq_sq_of_pos at h3
    obtain ⟨z, hz, h3⟩ := h3
    have l1: x < y := by
      nlinarith
    have l2: y < z := by
      nlinarith
    clear hb hc hy hz
    replace hx: 0 < x := by nlinarith
    replace l: 2 * (a + b + c) ≤ 108 := by omega
    rw [show 2 * (a + b + c) = x ^ 2 + y ^ 2 + z ^ 2 by rw [←h1, ←h2, ←h3]; ring] at l
    replace l1: x + 1 ≤ y := by omega
    replace l2: y + 1 ≤ z := by omega

    -- from l1 and l2 and h, we see that x ≤ 4, y ≤ 6 and z ≤ 10, hence we can check all cases
    have rx: x < 5 := by nlinarith
    have ry: y < 7 := by nlinarith
    have rz: z < 11 := by nlinarith
    interval_cases x <;> interval_cases y <;> interval_cases z <;> omega