import Mathlib

theorem algebra_12914 {a : ℕ+ → ℤ} (ha : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n)
    (ha1 : a 1 = 20) (ha2 : a 2 = 20) : a 10 - 3 * a 9 = -40 := by
        have ha3 : a 3 = 2 * a 2 + 3 * a 1 := ha 1
        rw [ha1, ha2] at ha3
        norm_num at ha3
        have ha4 : a 4 = 2 * a 3 + 3 * a 2 := ha 2
        rw [ha3, ha2] at ha4
        norm_num at ha4
        have ha5 : a 5 = 2 * a 4 + 3 * a 3 := ha 3
        rw [ha4, ha3] at ha5
        norm_num at ha5
        have ha6 : a 6 = 2 * a 5 + 3 * a 4 := ha 4
        rw [ha5, ha4] at ha6
        norm_num at ha6
        have ha7 : a 7 = 2 * a 6 + 3 * a 5 := ha 5
        rw [ha6, ha5] at ha7
        norm_num at ha7
        have ha8 : a 8 = 2 * a 7 + 3 * a 6 := ha 6
        rw [ha7, ha6] at ha8
        norm_num at ha8
        have ha9 : a 9 = 2 * a 8 + 3 * a 7 := ha 7
        rw [ha8, ha7] at ha9
        norm_num at ha9
        have ha10 : a 10 = 2 * a 9 + 3 * a 8 := ha 8
        rw [ha9, ha8] at ha10
        norm_num at ha10
        rw [ha10, ha9]
        norm_num