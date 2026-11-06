import Mathlib

theorem algebra_310802 (f : ℤ → ℤ) (hf : f = fun y => 6*y^4-35*y^3+62*y^2-35*y+6) :
    {y : ℤ | f y = 0}.encard = 2 := by
  have h1 : ∀ y : ℤ, f y = 6*y^4-35*y^3+62*y^2-35*y+6 := by
    simp [hf]
  have h2 : {y : ℤ | f y = 0} = {2, 3} := by
    ext y
    simp [h1]
    constructor
    · -- Assume f y = 0, need to show y ∈ {2, 3}.
      intro h
      have h_eq : 6*y^4-35*y^3+62*y^2-35*y+6 = 0 := by
        linarith
      have h_eq1 : (y - 2) * (y - 3) * (2 * y - 1) * (3 * y - 1) = 0 := by
        nlinarith [sq_nonneg (y * (y - 1)), sq_nonneg ((y - 2) * (y - 3)), sq_nonneg ((2 * y - 1) * (3 * y - 1)), sq_nonneg (y - 2), sq_nonneg (y - 3)]
      cases' (mul_eq_zero.mp h_eq1) with h_eq2 h_eq3
      · cases' (mul_eq_zero.mp h_eq2) with h_eq4 h_eq5
        · cases' (mul_eq_zero.mp h_eq4) with h_eq6 h_eq7
          · -- Case y - 2 = 0
            left
            linarith
          · -- Case y - 3 = 0
            right
            linarith
        · -- Case 2y - 1 = 0
          exfalso
          omega
      · -- Case 3y - 1 = 0
        exfalso
        omega
    · -- Assume y ∈ {2, 3}, need to show f y = 0.
      rintro (rfl | rfl)
      · -- Case y = 2
        norm_num
      · -- Case y = 3
        norm_num
  rw [h2]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop
  all_goals try rfl
  all_goals try norm_num
  all_goals try aesop