import Mathlib

theorem algebra_290406 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ p q, 0 < p → 0 < q → a (p + q) = a p * a q) (h8 : a 8 = 16) :
    a 10 = 32 := by 
  have ha1 : 0 < a 1 := ha 1
  have ha2 : 0 < a 2 := ha 2
  have ha4 : 0 < a 4 := ha 4
  have ha8 : 0 < a 8 := ha 8
  have h44 : a 8 = a 4 * a 4 := by
    specialize h 4 4 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  rw [h8] at h44
  have ha4_eq : a 4 = 4 := by
    nlinarith [h44, ha4]
  have h22 : a 4 = a 2 * a 2 := by
    specialize h 2 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  rw [ha4_eq] at h22
  have ha2_eq : a 2 = 2 := by
    nlinarith [h22, ha2]
  have h82 : a 10 = a 8 * a 2 := by
    specialize h 8 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  rw [h8, ha2_eq] at h82
  linarith