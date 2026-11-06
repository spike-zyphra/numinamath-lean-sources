import Mathlib

/- Four positive integers $A$, $B$, $C$ and $D$ have a sum of 36. If $A+2 = B-2 = C \times 2 = D \div 2$, what is the value of the product $A \times B \times C \times D$? -/
theorem algebra_10837 {A B C D : ℤ} (h₀ : A > 0) (h₁ : B > 0) (h₂ : C > 0) (h₃ : D > 0)
    (h₄ : A + B + C + D = 36) (h₅ : A + 2 = B - 2) (h₆ : B - 2 = C * 2) (h₇ : C * 2 = (D / 2:ℚ)) :
    A * B * C * D = 3840 := by
  -- substitute A,B in terms of C
  have b_of_c: B = C*2 + 2 := by
    have: B = B-2 + 2 := by ring
    rw [this, h₆]
  have a_of_c: A = C*2-2 := by
    have: A = A+2 - 2 := by ring
    rw [this, h₅,h₆]
  -- substitute D in terms of C.
  -- in fact, from 2C=D/2, we immediately get D=4C. however, we have to do some extra work in lean4.
  have d_of_c: D = C*4 := by
    have ht1: (D:ℚ) = C*4 := by
      have: (D:ℚ) = D/2 * 2 := by field_simp
      rw [this, ← h₇]; ring
    have ht2: Rat.ofInt D = Rat.ofInt (C*4) := by
      have: Rat.ofInt D = D := rfl
      rw [this, ht1]; simp
    symm
    exact Rat.intCast_inj.mp (id (Eq.symm ht2))
  -- substitute back to A+B+C+D=36, we get C=4
  have ceq: C = 4 := by
    rw [b_of_c,a_of_c,d_of_c] at h₄
    have ht1: C * 2 - 2 + (C * 2 + 2) + C + C * 4 = 9*C := by ring
    have ht2: (36:ℤ) = 9*4 := by norm_num
    rw [ht1, ht2] at h₄
    have ht3: C = 4 ∨ (9:ℤ) = 0 := mul_eq_mul_left_iff.mp h₄
    rcases ht3 with left | right
    exact left
    norm_num at right
  -- from C=4, solve A,B,D
  have beq: B = 10 := by
    rw [ceq] at b_of_c
    rw [b_of_c]; ring
  have aeq: A = 6 := by
    rw [ceq] at a_of_c
    rw [a_of_c]; ring
  have deq: D = 16 := by
    rw [ceq] at d_of_c
    rw [d_of_c]; ring
  -- A=6, B=10, C=4, D=16, then A * B * C * D = 6 * 10 * 4 * 16 = 3840
  rw [aeq,beq,ceq,deq]
  norm_num