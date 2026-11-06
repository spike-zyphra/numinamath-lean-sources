import Mathlib

theorem algebra_277547 :
  {(x, y, z) : ℝ × ℝ × ℝ | 
    (x + y - z ≠ 0) ∧ (x - y + z ≠ 0) ∧ (-x + y + z ≠ 0) ∧ (x + y + z ≠ 0) ∧
    (1 / (x + y - z) + 1 / (x - y + z) + 1 / (-x + y + z) = 1 / (x + y + z))} =
  {(x, y, z) : ℝ × ℝ × ℝ | 
    (x + y - z ≠ 0) ∧ (x - y + z ≠ 0) ∧ (-x + y + z ≠ 0) ∧ (x + y + z ≠ 0) ∧
    (x * y * z = 0)} := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h, prove h
    intro h
    rcases h with ⟨h1, h2, h3, h4, heq⟩
    have h_eq : (x - y + z) * (-x + y + z) * (x + y + z) + (x + y - z) * (-x + y + z) * (x + y + z) + (x + y - z) * (x - y + z) * (x + y + z) = (x + y - z) * (x - y + z) * (-x + y + z) := by 
      field_simp [(show x + y - z ≠ 0 by tauto), (show x - y + z ≠ 0 by tauto), (show -x + y + z ≠ 0 by tauto), (show x + y + z ≠ 0 by tauto)] at heq ⊢ 
      nlinarith [sq_pos_of_ne_zero (show x + y - z ≠ 0 by tauto), sq_pos_of_ne_zero (show x - y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show -x + y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show x + y + z ≠ 0 by tauto)]
    have h5 : x * y * z = 0 := by 
      nlinarith [sq_pos_of_ne_zero (show x + y - z ≠ 0 by tauto), sq_pos_of_ne_zero (show x - y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show -x + y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show x + y + z ≠ 0 by tauto), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z), sq_nonneg (x + y + z)]
    tauto
  · -- Assume h, prove h
    rintro ⟨h1, h2, h3, h4, heq⟩
    have h5 : (x - y + z) * (-x + y + z) * (x + y + z) + (x + y - z) * (-x + y + z) * (x + y + z) + (x + y - z) * (x - y + z) * (x + y + z) = (x + y - z) * (x - y + z) * (-x + y + z) := by 
      nlinarith [sq_pos_of_ne_zero (show x + y - z ≠ 0 by tauto), sq_pos_of_ne_zero (show x - y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show -x + y + z ≠ 0 by tauto), sq_pos_of_ne_zero (show x + y + z ≠ 0 by tauto), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z), sq_nonneg (x + y + z)]
    have heq : 1 / (x + y - z) + 1 / (x - y + z) + 1 / (-x + y + z) = 1 / (x + y + z) := by 
      field_simp [(show x + y - z ≠ 0 by tauto), (show x - y + z ≠ 0 by tauto), (show -x + y + z ≠ 0 by tauto), (show x + y + z ≠ 0 by tauto)]
      nlinarith
    tauto