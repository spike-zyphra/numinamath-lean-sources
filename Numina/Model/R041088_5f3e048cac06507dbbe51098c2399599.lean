import Mathlib


lemma lemma_1 (a x y : ℝ) (ha : a ≠ 0) (h1 : x + y = a)
    (h2 : x^3 + y^3 = a) : 3 * x * y = a^2 - 1 := by
  have h3 : x^3 + y^3 = (x + y) ^ 3 - 3 * x * y * (x + y) := by
    ring
  rw [h1] at h3
  have h4 : a = a^3 - 3 * x * y * a := by
    linarith [h2, h3]
  have h5 : a^3 - a = 3 * x * y * a := by
    linarith [h4]
  have h6 : a * (a^2 - 1) = 3 * x * y * a := by
    linarith [h5]
  have h7 : a^2 - 1 = 3 * x * y := by
    apply (mul_left_inj' ha).mp
    linarith [h6]
  linarith [h7]


theorem algebra_87556 : {a : ℝ | ∃ x y : ℝ, x + y = a ∧ x ^ 3 + y ^ 3 = a ∧ x ^ 5 + y ^ 5 = a} = {0, 1, -1, 2, -2} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward implication: if exists x, y satisfying the equations, then a in {0, ±1, ±2}
    rintro ⟨x, y, h₁, h₂, h₃⟩
    have eq1 : x ^ 5 + y ^ 5 = (x + y) ^ 5 - 5 * (x * y) * (x + y) ^ 3 + 5 * (x * y) ^ 2 * (x + y) := by
      ring
    rw [h₁] at eq1
    have eq2 : a = a^5 - 5 * (x * y) * a^3 + 5 * (x * y) ^ 2 * a := by
      nlinarith [h₃, eq1]

    have eq5 : a * (a^4 - 5 * a^2 + 4) = 0 := by
      by_cases ha' : a = 0
      · -- If a = 0, then 0 * (0^4 - 5*0^2 + 4) = 0
        rw [ha']
        norm_num
      · -- a ≠ 0, so we can use lemma_1
        have h3xy : 3 * x * y = a^2 - 1 := by
          apply lemma_1 a x y (show a ≠ 0 by
            intro h
            apply ha'
            linarith
          ) h₁ h₂
        have eq4 : a = a^5 - 5 * (x * y) * a^3 + 5 * (x * y) ^ 2 * a := by
          nlinarith [h₃, eq1]
        -- Simplify using the relation from lemma_1
        have h4 : x * y = (a^2 - 1)/3 := by
          linarith [h3xy]
        rw [show x * y = (a^2 -1)/3 by linarith [h3xy]] at eq4
        nlinarith [sq_pos_of_pos (show 0 < 2 by norm_num)]
    
    cases' (mul_eq_zero.1 eq5) with h41 h42
    · -- case a = 0
      left
      exact h41
    · -- case a^4 -5 a^2 +4 =0
      have h5 : a^4 -5*a^2 +4 =0 := by
        nlinarith
      have h6 : a^4 -5*a^2 +4 = (a^2 -1)*(a^2 -4) := by
        nlinarith
      rw [h6] at h5
      cases' (mul_eq_zero.1 h5) with h51 h52
      · -- a^2 -1 = 0.
        have h7 : a^2 =1 := by
          nlinarith
        have h8 : a =1 ∨ a =-1 := by
          rw [sq_eq_one_iff] at h7
          tauto
        cases' h8 with ha1 ha2
        · -- a =1
          right
          left
          exact ha1
        · -- a = -1
          right
          right
          left
          linarith
      · -- a^2 -4 =0.
        have h8 : a^2 =4 := by
          nlinarith
        have h9 : a =2 ∨ a =-2 := by
          have h91 : a^2 =4 := by
            nlinarith
          have : a = 2 ∨ a = -2 := by
            have h : a^2 - 4 = 0 := by nlinarith
            have : (a - 2) * (a + 2) = 0 := by nlinarith
            cases' (mul_eq_zero.1 this) with h10 h11
            · -- a -2 =0.
              left
              linarith
            · -- a +2 =0.
              right
              linarith
          tauto
        cases' h9 with ha1 ha2
        · -- a =2
          right
          right
          right
          left
          linarith
        · -- a = -2
          right
          right
          right
          right
          linarith
  · -- Backward direction: each a in {0, ±1, ±2} has a solution.
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- a =0
      use 1, -1
      norm_num
    · -- a =1
      use 1, 0
      norm_num
    · -- a =-1
      use -1, 0
      norm_num
    · -- a =2
      use 1, 1
      norm_num
    · -- a =-2
      use -1, -1
      norm_num