import Mathlib

open Real Set
open scoped BigOperators

/- Find all values of the parameter $a$, for each of which the equation $a|2-x|+\frac{x^{2}-x-6}{3-x}=0$ has exactly one solution -/
theorem algebra_144723: {a: ℝ | ∃! x: ℝ, x ≠ 3 ∧ a * abs (2 - x) + (x ^ 2 - x - 6) / (3 - x) = 0}
= Ioc (-1) 1 ∪ {5} := by

  -- we first show a simp identity that will be used many times later
  have s: ∀ z: ℝ, z ≠ 3 → (z ^ 2 - z - 6) / (3 - z) = - z - 2 := by
    intro z
    intro h
    rw [show z ^ 2 - z - 6 = (z + 2) * (z - 3) by ring]
    replace h: 3 - z ≠ 0 := by
      by_contra! no
      replace no: z = 3 := by linarith
      simp [no] at h
    field_simp
    ring

  ext a
  constructor
  -- the foward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨x, h1, h2⟩ := h
    rcases h1 with ⟨hx, h⟩
    by_contra! h  --for convenience, we prove by contradiction
    simp at h
    rcases h with ⟨a1, a2⟩


    by_cases l: a ≤ - 1
    -- case 1: a ≤ -1
    .
      have o: a ≠ - 1 := by  --show a ≠ -1
        by_contra! no
        clear h2
        specialize s x
        simp [h,hx] at s
        rw [s] at h
        replace h: a * abs (2 - x) = x + 2 := by linarith
        have o: x + 2 ≤ 0 := by
          rw [← h]
          have o1: 0 ≤ |2 - x| := by
            simp
          have o2: a ≤ -1 := by linarith
          nlinarith
        replace o: 0 ≤ 2 - x := by linarith
        rw [show |2 - x| = 2 - x by apply abs_of_nonneg; exact o] at h
        simp [no] at h
        linarith
      clear h2
      specialize s x
      simp [h,hx] at s
      rw [s] at h
      replace h: a * abs (2 - x) = x + 2 := by linarith
      have r: x + 2 ≤ 0 := by
        rw [← h]
        have r1: 0 ≤ |2 - x| := by
         simp
        have r2: a ≤ 0 := by linarith
        apply mul_nonpos_of_nonpos_of_nonneg
        exact r2
        exact r1
      rw [show |2 - x| = 2 - x by apply abs_of_nonneg; linarith] at h
      nlinarith  -- h and r implies contradiction by 0 ≤ a ∧ a ≤ -1
    -- case 2: a > -1
    .
      simp at l
      simp [l] at a2
      clear l
      -- then we that 2a + 2 / a - 1 and 2a - 2 / a + 1 are two different solutions
      have e1: (2 * a + 2) / (a - 1) = x := by  -- show (2a + 2) / (a - 1) = x
        specialize h2 ((2 * a + 2) / (a - 1))
        apply h2
        have i: a - 1 ≠ 0 := by
            by_contra! no
            replace no: a = 1 := by linarith
            simp [no] at a2
        have j: (2 * a + 2) / (a - 1) ≠ 3 := by
          field_simp
          by_contra! j
          replace j: a = 5 := by nlinarith
          simp [j] at a1
        constructor
        .
          exact j
        .
          specialize s ((2 * a + 2) / (a - 1))
          simp [j] at s
          rw [s]
          clear s
          have q: 2 - (2 * a + 2) / (a - 1) ≤ 0 := by
            have o: 2 - (2 * a + 2) / (a - 1) = -4 / (a - 1) := by
               field_simp
               ring
            rw [o]
            apply div_nonpos_of_nonpos_of_nonneg
            norm_num
            linarith
          rw [show |2 - (2 * a + 2) / (a - 1)| = -(2 - (2 * a + 2) / (a - 1)) by apply abs_of_nonpos; linarith]
          field_simp
          ring

      have e2: (2 * a - 2) / (a + 1) = x := by  -- show (2a - 2) / (a + 1) = x
        specialize h2 ((2 * a - 2) / (a + 1))
        apply h2
        have i: a + 1 ≠ 0 := by
            by_contra! no
            replace no: a = -1 := by linarith
            simp [no] at a2
            norm_num at a2
        have j: (2 * a - 2) / (a + 1) ≠ 3 := by
          field_simp
          by_contra! j
          replace j: a = - 5 := by nlinarith
          simp [j] at a2
          norm_num at a2
        constructor
        .
          exact j
        .
          specialize s ((2 * a - 2) / (a + 1))
          simp [j] at s
          rw [s]
          clear s
          have q: 0 ≤ 2 - (2 * a - 2) / (a + 1) := by
            have o: 2 - (2 * a - 2) / (a + 1) = 4 / (a + 1) := by
               field_simp
               ring
            rw [o]
            apply div_nonneg
            norm_num
            linarith
          rw [show |2 - (2 * a - 2) / (a + 1)| = (2 - (2 * a - 2) / (a + 1)) by apply abs_of_nonneg; linarith]
          field_simp
          ring

      -- then we arrive at the contradiction by combine e1 and e2
      clear h2 s h
      rw [← e2] at e1
      have i1: a - 1 ≠ 0 := by
        by_contra! no
        replace no: a = 1 := by linarith
        simp [no] at a2
      have i2: a + 1 ≠ 0 := by
        by_contra! no
        replace no: a = -1 := by linarith
        simp [no] at a2
        norm_num at a2
      field_simp at e1
      ring_nf at e1
      simp at e1
      replace e1: a = 5 := by nlinarith
      tauto


  -- the backward direction
  .
    intro h
    simp at h
    simp only [Set.mem_setOf_eq]
    use (2 * a - 2) / (a + 1)  -- we show that (2a - 2) / (a + 1) is the unique solution
    constructor
    .  --show it's indeed a solution
      simp
      have i: a + 1 ≠ 0 := by
        by_contra! no
        replace no: a = -1 := by linarith
        simp [no] at h
        norm_num at h
      have j: (2 * a - 2) / (a + 1) ≠ 3 := by
        field_simp
        by_contra! j
        replace j: a = -5 := by nlinarith
        simp [j] at h
        norm_num at h
      simp [j]
      specialize s ((2 * a - 2) / (a + 1))
      simp [j] at s
      rw [s]
      clear s
      have q: 0 ≤ 2 - (2 * a - 2) / (a + 1) := by
          have o: 2 - (2 * a - 2) / (a + 1) = 4 / (a + 1) := by
             field_simp
             ring
          rw [o]
          apply div_nonneg
          norm_num
          rcases h with h | h
          . linarith
          . linarith
      rw [show |2 - (2 * a - 2) / (a + 1)| = (2 - (2 * a - 2) / (a + 1)) by apply abs_of_nonneg; linarith]
      field_simp
      ring
    . -- show it's unique
      intro y h1
      rcases h1 with ⟨hy, h1⟩
      specialize s y
      simp [hy] at s
      rw [s] at h1
      clear s
      replace h1: a * abs (2 - y) = y + 2 := by linarith
      rcases h with h | h
      -- case a = 5
      .
        simp [h] at *
        by_cases ly: y ≤ 2
        .
          rw [show |2 - y| = 2 - y by apply abs_of_nonneg; linarith] at h1
          norm_num
          linarith
        .
          simp at ly
          rw [show |2 - y| = -(2 - y) by apply abs_of_nonpos; linarith] at h1
          norm_num
          replace h1: y = 3 := by nlinarith
          tauto
      -- case -1 < a ≤ 1
      .
        rcases h with ⟨a1,a2⟩
        by_cases ly: y ≤ 2
        .
          rw [show |2 - y| = 2 - y by apply abs_of_nonneg; linarith] at h1
          have i: a + 1 ≠ 0 := by
            by_contra! no
            replace no: a = -1 := by linarith
            simp [no] at h1
            nlinarith
          field_simp
          nlinarith
        .
          simp at ly
          rw [show |2 - y| = -(2 - y) by apply abs_of_nonpos; linarith] at h1
          have i: a + 1 ≠ 0 := by
            by_contra! no
            replace no: a = -1 := by linarith
            simp [no] at h1
            nlinarith
          field_simp
          nlinarith
