import Mathlib

open Polynomial

/-Let P(x) be a polynomial of degree at most 3 such that
P(x) = 1/(1+x+x^2) for x = 1, 2, 3, 4. What is P(5)?-/
theorem algebra_608764 {P: ℝ[X]} (h_deg: P.natDegree ≤ 3) (h1: P.eval 1 = 1 / (1 + 1 + 1 ^ 2))
  (h2: P.eval 2 = 1 / (1 + 2 + 2 ^ 2)) (h3: P.eval 3 = 1 / (1 + 3 + 3 ^ 2))
  (h4: P.eval 4 = 1 / (1 + 4 + 4 ^ 2)): P.eval 5 = - 3 / 91 := by
    norm_num at h1 h2 h3 h4
    let Q: ℝ[X] := X ^ 3 * C (-4 / 273) + X ^ 2 * C (41 / 273) + X * C (-7 / 13) + C (67 / 91)
    let R: ℝ[X] := P - Q -- we show that P is indeed equal to Q
    have hR: R = 0 := by
      by_contra! ne
      have contra:= Polynomial.card_roots' R
      have hR_deg: R.natDegree ≤ 3 := by
        simp [R]
        have i:= Polynomial.natDegree_sub_le P Q
        have Q_deg: Q.natDegree = 3 := by
          simp [Q]
          compute_degree!
        have o: P.natDegree ⊔ Q.natDegree ≤ 3 := by
          simp
          constructor
          . linarith
          . linarith
        nlinarith [o,i]
      replace contra: R.roots.card ≤ 3 := by linarith -- where we arrive at the contradiction
      replace contra: ¬ 4 ≤ R.roots.card := by omega
      absurd contra
      have r1: 1 ∈ R.roots := by
        simp [ne,R]
        rw [h1]
        simp [Q]
        norm_num
      have r2: 2 ∈ R.roots := by
        simp [ne,R]
        rw [h2]
        simp [Q]
        norm_num
      have r3: 3 ∈ R.roots := by
        simp [ne,R]
        rw [h3]
        simp [Q]
        norm_num
      have r4: 4 ∈ R.roots := by
        simp [ne,R]
        rw [h4]
        simp [Q]
        norm_num
      have o: {1,2,3,4} ≤ R.roots := by
        have i: ({1,2,3,4}: Multiset ℝ).Nodup := by
          simp
        have j: ({1,2,3,4}: Multiset ℝ) ≤ R.roots ↔ ({1,2,3,4}: Multiset ℝ) ⊆ R.roots := by
          apply Multiset.le_iff_subset
          exact i
        rw [j]
        simp [*]
      have r:= Multiset.card_le_card o
      have o1: ({1,2,3,4}: Multiset ℝ).card = 4 := by
        norm_num
      rw [o1] at r
      exact r
    simp [R] at hR
    replace hR: P = Q := by
      rw [show P = P - Q + Q by ring]
      rw [hR]
      simp
    rw [hR]
    simp [Q]
    norm_num