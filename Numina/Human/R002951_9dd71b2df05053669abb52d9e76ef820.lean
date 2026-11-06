import Mathlib

open Polynomial


-- 4. How many polynomials $p(x)$ of second degree, with integer coefficients and 2 integer roots, are there such that $p(8)=1$? (Note: remember that integers can be positive, negative, or zero)
-- (A) 1
-- (B) 2
-- (C) 3
-- (D) a finite number greater than 3
-- (E) infinitely many.

theorem algebra_134635 (S : Set (ℤ[X]))
  (hS : S = {p : ℤ[X] | p.natDegree = 2 ∧ p.eval 8 = 1 ∧ p.roots.card = 2 ∧ ∀ r ∈ p.roots, ∃ n : ℤ, r = n}) :
  S.encard = 3 := by

  suffices S = {
    (X - C 7) ^ 2,
    (X - C 9) ^ 2,
    - (X - C 7) * (X - C 9)
  } by
    rw [this]
    rw [Set.encard_insert_of_not_mem]
    rw [Set.encard_pair]
    . norm_num
    . by_contra h
      ring_nf at h
      have : (-(X * C 9 * 2: ℤ[X]) + X ^ 2 + C 9 ^ 2).coeff 0 = (X * C 9 + X * C 7 + (-X ^ 2 - C 9 * C 7: ℤ[X])).coeff 0 := by
        rw [h]

      simp at this
      norm_num at this

    . simp
      constructor
      . by_contra h
        have : ((X - 7) ^ 2 : ℤ[X]).coeff 0 = ((X - 9) ^ 2 : ℤ[X]).coeff 0 := by
          rw [h]

        ring_nf at this
        simp at this


      . by_contra h
        have : ((X - 7) ^ 2 : ℤ[X]).coeff 0 = ((7 - X) * (X - 9) : ℤ[X]).coeff 0 := by
          rw [h]

        ring_nf at this
        norm_num at this


  rw [hS]
  ext p
  simp
  constructor
  . intro ⟨h1, h2, h3⟩
    have hroots: p.roots.card = p.natDegree := by
      rw [h3, h1]

    rw [Multiset.card_eq_two] at h3
    obtain ⟨m, n, h3⟩ := h3
    let a := p.leadingCoeff

    have h4 : p = a * ((X -C m):ℤ[X]) * ((X -C n):ℤ[X]) := by
      have := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
      rw [h3] at this
      simp at this
      rw [← this]
      unfold a
      simp
      rw [mul_assoc]

    rw [h4] at h2
    rw [eval_mul] at h2
    simp at h2
    let s := 8 - m
    let t := 8 - n

    replace h2 : a * s * t = 1 := by
      simp only [s, t]
      exact h2

    have ha: a = 1 ∨ a = -1 := by
      rw [mul_assoc] at h2
      exact Int.eq_one_or_neg_one_of_mul_eq_one h2

    have hs: s = 1 ∨ s = -1 := by
      have h_perm : s * (a * t) = 1 := by
        calc s * (a * t) = s * a * t := by rw [← mul_assoc]
          _ = a * s * t := by rw [mul_comm s a, mul_assoc]
          _ = 1 := h2
      exact Int.eq_one_or_neg_one_of_mul_eq_one h_perm

    rcases ha with ha | ha
    . rcases hs with hs | hs
      . have ht : t = 1 := by
          rw [ha, hs] at h2
          norm_num at h2
          exact h2
        left
        simp only [h4, ha, hs, ht, s, t]
        simp
        norm_cast
        unfold s at hs
        unfold t at ht
        have : m = 7 := by linarith
        rw [this]
        have : n = 7 := by linarith
        rw [this]
        ring_nf

      . have ht : t = -1 := by
          rw [ha, hs] at h2
          norm_num at h2
          linarith
        right; left
        simp only [h4, ha, hs, ht, s, t]
        simp
        norm_cast
        unfold s at hs
        unfold t at ht
        have : m = 9 := by linarith
        rw [this]
        have : n = 9 := by linarith
        rw [this]
        ring_nf

    . right; right
      rcases hs with hs | hs
      . have ht : t = -1 := by
          rw [ha, hs] at h2
          norm_num at h2
          linarith
        simp only [h4, ha, hs, ht, s, t]
        simp
        norm_cast
        unfold s at hs
        unfold t at ht
        have : m = 7 := by linarith
        rw [this]
        have : n = 9 := by linarith
        rw [this]
        ring_nf

      . have ht : t = 1 := by
          rw [ha, hs] at h2
          norm_num at h2
          linarith
        simp only [h4, ha, hs, ht, s, t]
        simp
        norm_cast
        unfold s at hs
        unfold t at ht
        have : m = 9 := by linarith
        rw [this]
        have : n = 7 := by linarith
        rw [this]
        ring_nf

  . intro h
    refine ⟨?_, ?_, ?_⟩
    . rcases h with rfl | rfl | rfl
      all_goals try simp
      all_goals try apply natDegree_X_sub_C
      rw [natDegree_mul]
      . have : ((X - C 9) : ℤ[X]).natDegree = 1 := by
          apply natDegree_X_sub_C
        simp at this
        rw [this]

        have : (-(X - C 7) : ℤ[X]).natDegree = 1 := by
          rw [natDegree_neg]
          apply natDegree_X_sub_C
        simp at this
        rw [this]

      . by_contra h
        have := X_sub_C_ne_zero (7:ℤ)
        simp at this
        rw [← neg_eq_zero] at h
        simp at h
        contradiction
      . have := X_sub_C_ne_zero (9:ℤ)
        simp at this
        exact this

    . rcases h with rfl | rfl | rfl
      all_goals simp
    . rcases h with rfl | rfl | rfl
      . simp
        have : ((X - C 7) : ℤ[X]).roots.card = 1 := by
          rw [roots_X_sub_C]
          simp
        simp at this
        rw [this]

      . simp
        have : ((X - C 9) : ℤ[X]).roots.card = 1 := by
          rw [roots_X_sub_C]
          simp
        simp at this
        rw [this]

      . have : (7 - X) * ((X - 9):ℤ[X]) ≠ 0 := by
          by_contra h
          simp at h
          rcases h with h | h
          . have := X_sub_C_ne_zero (7:ℤ)
            simp at this
            rw [← neg_eq_zero] at h
            simp at h
            contradiction

          . have := X_sub_C_ne_zero (9:ℤ)
            simp at this
            contradiction

        rw [roots_mul this]
        simp
        have : (-(X - C 7) : ℤ[X]).roots.card = 1 := by
          rw [roots_neg, roots_X_sub_C]
          simp
        simp at this
        rw [this]

        have : ((X - C 9) : ℤ[X]).roots.card = 1 := by
          rw [roots_X_sub_C]
          simp
        simp at this
        rw [this]
