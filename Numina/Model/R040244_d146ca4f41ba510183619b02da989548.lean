import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) :
  sin (2 * arctan x) = 2 * x / (1 + x ^ 2) := by
  have h1 : sin (2 * arctan x) = 2 * sin (arctan x) * cos (arctan x) := by
    rw [sin_two_mul]
  have h2 : sin (arctan x) = x / Real.sqrt (1 + x^2) := by
    rw [sin_arctan]
  have h3 : cos (arctan x) = 1 / Real.sqrt (1 + x^2) := by
    rw [cos_arctan]
  rw [h1, h2, h3]
  have h4 : 0 < (Real.sqrt (1 + x^2) : ℝ) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg x]
  have h5 : Real.sqrt (1 + x^2) * Real.sqrt (1 + x^2) = 1 + x^2 := by
    calc
      Real.sqrt (1 + x^2) * Real.sqrt (1 + x^2) = (Real.sqrt (1 + x^2)) ^ 2 := by ring
      _ = 1 + x^2 := by rw [Real.sq_sqrt]; positivity
  field_simp [h4, h5]
  all_goals ring


theorem calculus_23390 : {x | sin (4 * arctan x) = 24 / 25} = {-3, -2, 1 / 3, 1 / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  have h11 : sin (4 * arctan x) = 2 * sin (2 * arctan x) * cos (2 * arctan x) := by
    have h12 : sin (4 * arctan x) = sin (2 * (2 * arctan x)) := by ring_nf
    rw [h12]
    rw [sin_two_mul]
  have h12 : sin (4 * arctan x) = 4 * x * (1 - x^2) / (1 + x^2)^2 := by
    rw [h11]
    have h13 : sin (2 * arctan x) = 2 * x / (1 + x^2) := by
      apply lemma_1
    have h14 : cos (2 * arctan x) = (1 - x^2) / (1 + x^2) := by
      have h15' (y : ℝ) : cos (2 * arctan y) = (1 - y^2) / (1 + y^2) := by
        have h16 : cos (2 * arctan y) = 1 - 2 * sin (arctan y)^2 := by
          have h17 : cos (2 * arctan y) = 1 - 2 * sin (arctan y) ^ 2 := by
            rw [cos_two_mul, sin_sq]
            all_goals ring
          linarith
        have h17 : sin (arctan y) = y / Real.sqrt (1 + y^2) := by
          rw [sin_arctan]
        have h18 : sin (arctan y) ^ 2 = y^2 / (1 + y^2) := by
          rw [h17]
          have h19 : 0 < (Real.sqrt (1 + y^2) : ℝ) := by
            apply Real.sqrt_pos.mpr
            nlinarith [sq_nonneg y]
          have h20 : Real.sqrt (1 + y^2) ^ 2 = 1 + y^2 := by
            rw [Real.sq_sqrt]
            positivity
          field_simp [h19, h20]
          all_goals nlinarith
        rw [h18] at h16
        field_simp at h16 ⊢
        nlinarith
      specialize h15' x
      simpa using h15'
    rw [h13, h14]
    field_simp
    all_goals ring_nf
  rw [h12]
  constructor
  · -- Assume $ \sin (4 \arctan x) = \frac{24}{25}$, prove $x \in \{-3, -2, 1/3, 1/2\}$.
    intro h
    have h23 : 1 + x^2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    have h24 : 25 * (4 * x * (1 - x^2)) = 24 * (1 + x^2)^2 := by
      field_simp at h ⊢
      nlinarith
    have h27 : (x - 1/2) * (x - 1/3) * (x + 2) * (x + 3) = 0 := by
      have h28 : 24 * x^4 + 100 * x^3 + 48 * x^2 - 100 * x + 24 = 0 := by
        nlinarith
      have h29 : 24 * x^4 + 100 * x^3 + 48 * x^2 - 100 * x + 24 = 
        24 * ((x - 1/2) * (x - 1/3) * (x + 2) * (x + 3)) := by
        ring
      rw [h29] at h28
      have h30 : (x - 1/2) * (x - 1/3) * (x + 2) * (x + 3) = 0 := by
        linarith
      exact h30
    cases' (mul_eq_zero.mp h27) with h28 h29
    cases' (mul_eq_zero.mp h28) with h30 h31
    cases' (mul_eq_zero.mp h30) with h32 h33
    · -- Case $x - 1/2 = 0$, so $x = 1/2$
      have h34 : x = 1/2 := by linarith
      simp [h34]
    · -- Case $x - 1/3 = 0$, so $x = 1/3$
      have h34 : x = 1/3 := by linarith
      simp [h34]
    · -- Case $x + 2 = 0$, so $x = -2$
      have h34 : x = -2 := by linarith
      simp [h34]
    · -- Case $x + 3 = 0$, so $x = -3$
      have h34 : x = -3 := by linarith
      simp [h34]
  · -- Assume $x \in \{-3, -2, 1/3, 1/2\}$, prove $ \sin (4 \arctan x) = \frac{24}{25}$.
    rintro (rfl | rfl | rfl | rfl)
    · -- x = -3
      norm_num [Real.sin_arctan, Real.cos_arctan, mul_add, mul_comm, mul_assoc, Real.sin_arctan, Real.cos_arctan]
    · -- x = -2
      norm_num [Real.sin_arctan, Real.cos_arctan, mul_add, mul_comm, mul_assoc, Real.sin_arctan, Real.cos_arctan]
    · -- x = 1/3
      norm_num [Real.sin_arctan, Real.cos_arctan, mul_add, mul_comm, mul_assoc, Real.sin_arctan, Real.cos_arctan]
    · -- x = 1/2
      norm_num [Real.sin_arctan, Real.cos_arctan, mul_add, mul_comm, mul_assoc, Real.sin_arctan, Real.cos_arctan]