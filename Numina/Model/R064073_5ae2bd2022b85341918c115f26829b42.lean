import Mathlib

def isLucky (n : ℕ) := n = 19 * (Nat.digits 10 n).sum

theorem number_theory_302004 :
    {n | n ∈ Finset.Icc 1 999 ∧ isLucky n} =
    {114, 133, 152, 171, 190, 209, 228, 247, 266, 285, 399} := by 
  ext n
  simp [isLucky, Finset.mem_Icc]
  constructor
  · -- Forward direction: if n in {n | n ∈ [1, 999] ∧ n =19*(sum digits)}, then n in {114, 133, 152, 171, 190, 209, 228, 247, 266, 285, 399}
    rintro ⟨⟨hn1, hn2⟩, h⟩
    interval_cases n <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction: if n in {114, 133, 152, 171, 190, 209, 228, 247, 266, 285, 399}, then n in {n | n ∈ [1, 999] ∧ isLucky n}
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]
    · constructor <;> norm_num [isLucky]