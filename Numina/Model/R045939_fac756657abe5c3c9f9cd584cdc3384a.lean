import Mathlib

theorem algebra_288169 :
  {t : ℝ | ∃ (right_eye left_eye right_leg throat : ℝ),
    right_eye = 48 ∧ left_eye = 72 ∧ right_leg = 96 ∧ throat = 6 ∧
    t = 1 / (1/right_eye + 1/left_eye + 1/right_leg + 1/throat)} =
  {288 / 61} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward direction
    rintro ⟨right_eye, left_eye, right_leg, throat, h1, h2, h3, h4, ht⟩
    rw [ht]
    rw [h1, h2, h3, h4]
    norm_num
  · -- Backward direction
    intro ht
    rw [ht]
    use 48, 72, 96, (6 : ℝ)
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    field_simp
    <;> norm_num