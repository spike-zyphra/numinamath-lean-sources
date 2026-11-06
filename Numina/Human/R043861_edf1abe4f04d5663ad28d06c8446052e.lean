import Mathlib

theorem algebra_158937 {a : PNat → ℤ} (apos : ∀ n, 0 < a n)
  (ainc : ∀ n, a n < a (n + 1))
  (ha : ∀ n, a (n + 2) = a (n + 1) + a n)
  (a7eq : a 7 = 120) : a 8 = 194 := by

  have ha3: a 3 = a 2 + a 1 := ha 1
  have ha4: a 4 = a 3 + a 2 := ha 2
  have ha5: a 5 = a 4 + a 3 := ha 3
  have ha6: a 6 = a 5 + a 4 := ha 4
  have ha7: a 7 = a 6 + a 5 := ha 5
  have ha8: a 8 = a 7 + a 6 := ha 6

  replace ha7: a 7 = 8 * a 2 + 5 * a 1 := by
    rw [ha7, ha6, ha5, ha4, ha3]
    ring
  replace ha8: a 8 = 13 * a 2 + 8 * a 1 := by
    rw [ha8, ha7, ha6, ha5, ha4, ha3]
    ring

  have a1lta2: a 1 < a 2 := ainc 1

  have a2_lb: a 2 ≥ 10 := by
    have: a 2 > 9 := by
      by_contra! a2le
      have: (120:ℤ) ≤ 117 := calc
        120 = a 7 := a7eq.symm
        _ = 8 * a 2 + 5 * a 1 := ha7
        _ ≤ 8 * a 2 + 5 * a 2 := by linarith [a1lta2]
        _ = 13 * a 2 := by ring
        _ ≤ 117 := by linarith [a2le]
      norm_num at this
    exact this

  have a2_ub: a 2 ≤ 14 := by
    have: 8 * a 2 < 120 := by
      rw [← a7eq, ha7]
      linarith only [apos 1]
    linarith only [this]

  have hdvd: 5 ∣ 120 - 8 * a 2 := by
    rw [← a7eq, ha7]
    use (a 1)
    ring

  have a2eq: a 2 = 10 := by
    interval_cases (a 2)
    · rfl
    all_goals norm_num at hdvd

  have a1eq: a 1 = 8 := by
    rw [a7eq, a2eq] at ha7
    linarith only [ha7]

  norm_num [ha8, a1eq, a2eq]