import Mathlib

theorem algebra_98040 {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (h : Nat.choose 9 1 * (p ^ 8 * q) = Nat.choose 9 2 * (p ^ 7 * q ^ 2)) :
    p = 4 / 5 := by

  have h1 : (Nat.choose 9 1 : ℝ) = 9 := by
    norm_num [Nat.choose]

  have h2 : (Nat.choose 9 2 : ℝ) = 36 := by
    norm_num [Nat.choose]

  rw [h1] at h
  rw [h2] at h

  have eq1 : 9 * (p ^ 8 * q) = 36 * (p ^ 7 * q ^ 2) := by
    norm_num at h ⊢
    linarith

  have eq2 : p ^ 7 * (p * q - 4 * q ^ 2) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- Case p^7 = 0
    have h4 : p = 0 := by
      have h3' : p ^ 7 = 0 := by
        simpa using h3
      have h5 : p ^ 7 = 0 := h3'
      simp at h5 ⊢
      <;> nlinarith
      <;> nlinarith
    linarith -- contradicts hp
  · -- Case p * q - 4 * q^2 = 0
    have eq3 : p * q - 4 * q ^ 2 = 0 := by
      linarith

    have eq4 : p = 4 * q := by
      apply (mul_left_inj' (ne_of_gt hq)).mp
      linarith

    have eq5 : q = 1 / 5 := by
      nlinarith [hsum, eq4]

    have eq6 : p = 4 / 5 := by
      nlinarith [eq4, eq5]

    linarith [eq6]