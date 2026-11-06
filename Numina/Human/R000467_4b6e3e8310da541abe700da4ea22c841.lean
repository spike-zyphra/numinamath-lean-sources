import Mathlib

/-The square root of $x$ is greater than 3 and less than 4. How many integer values of $x$ satisfy this condition?-/
theorem algebra_10983 : Set.ncard {x : ℤ | 3 < Real.sqrt x ∧ Real.sqrt x < 4} = 6 := by
  -- Because $4 > \sqrt{x} > 3$, we know that $16 > x > 9$.  Thus, the integers from 10 to 15 inclusive satisfy this inequality, which means $\boxed{6}$ integers satisfy the condition in the problem.
  have : {x : ℤ | 3 < Real.sqrt x ∧ Real.sqrt x < 4} = {x : ℤ | 9 < x ∧ x < 16} := by
    ext x
    simp
    constructor
    . rintro ⟨h1, h2⟩
      constructor
      . rw [Real.lt_sqrt (by linarith)] at h1
        norm_num at h1
        norm_cast at h1
      . rw [Real.sqrt_lt _ (by linarith)] at h2
        norm_num at h2
        norm_cast at h2
        have : 0 < √x := by linarith
        simp at this
        simp
        exact this.le
    . rintro ⟨h1, h2⟩
      constructor
      . rw [Real.lt_sqrt (by linarith)]
        norm_cast
      . rw [Real.sqrt_lt _ (by linarith)]
        norm_cast
        norm_cast
        linarith
  rw [this, Set.ncard_eq_of_bijective]
  exact λn (hn) ↦ (n + 10 : ℤ)
  simp
  intro a h1 h2
  use (a - 10).toNat
  constructor
  . rw [Int.toNat_lt (by linarith)]
    norm_cast
    linarith
  . have : (a - 10).toNat = a - 10 := by
      exact Int.toNat_sub_of_le h1
    rw [this]
    linarith

  intro i hi
  simp
  constructor
  repeat norm_cast; linarith

  intro i j _ _ hij
  simp at hij
  exact hij
