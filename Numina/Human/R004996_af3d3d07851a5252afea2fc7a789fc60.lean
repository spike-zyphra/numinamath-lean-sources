import Mathlib

/- Find all ordered triples $(x, y, z)$ of real numbers which satisfy the following system of equations:

$$
\left\{\begin{array}{l}
x y=z-x-y \\
x z=y-x-z \\
y z=x-y-z
\end{array}\right.
$$ -/
theorem algebra_604974 :
  { (x, y, z) : ℝ × ℝ × ℝ | x * y = z - x - y ∧ x * z = y - x - z ∧ y * z = x - y - z } = { (-2, 0, -2), (-2, -2, 0), (0, 0, 0), (0, -2, -2), (-1, -1, -1) } := by
  ext ⟨x, y, z⟩
  simp
  constructor
  -- We first verify that the given solutions satisfy the system of equations.
  swap
  . rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      norm_num
  -- Suppose x, y, z satisfy the system of equations.
  . rintro ⟨h₁, h₂, h₃⟩
    -- Subtracting the second equation from the first gives ( x y - x z = 2 z - 2 y ). Factoring ( y - z ) from each side and rearranging gives
    have h₄ : (x + 2) * (y - z) = 0 := by linear_combination h₁ - h₂
    simp at h₄
    -- So either ( x = -2 ) or ( z = y ).
    rcases h₄ with h₄ | h₄
    . -- If ( x = -2 ), the first equation becomes ( -2 y = z + 2 - y ), or ( y + z = -2 ). Substituting ( x = -2, y + z = -2 ) into the third equation gives ( y z = -2 - (-2) = 0 ). Hence either ( y ) or ( z ) is 0, so if ( x = -2 ), the only solutions are ( (-2, 0, -2) ) and ( (-2, -2, 0) ).
      replace h₄ : x = -2 := by linear_combination h₄
      subst h₄
      have h₄ : y + z = -2 := by linear_combination -h₁
      have h₅ : y * z = 0 := by linear_combination h₃ - h₄
      simp at h₅
      rcases h₅ with rfl | rfl
      all_goals
        simp
        linarith
    . -- If ( z = y ), the first equation becomes ( x y = -x ), or ( x(y + 1) = 0 ). If ( x = 0 ) and ( z = y ), the third equation becomes ( y^2 = -2 y ) which gives ( y = 0 ) or ( y = -2 ). If ( y = -1 ) and ( z = y = -1 ), the third equation gives ( x = -1 ). So if ( y = z ), the only solutions are ( (0, 0, 0) ), ( (0, -2, -2) ) and ( (-1, -1, -1) ).
      rw [sub_eq_zero] at h₄
      subst h₄
      replace h₁ : x * (y + 1) = 0 := by linear_combination h₁
      simp at h₁
      -- x = 0 or y = -1.
      rcases h₁ with rfl | h₁
      . simp at *
        replace h₃ : y * (y + 2) = 0 := by linear_combination h₃
        simp at h₃
        -- y = 0 or y = -2.
        rcases h₃ with rfl | h₃
        . simp
        . right
          linarith
      . replace h₁ : y = -1 := by linear_combination h₁
        subst h₁
        simp at *
        linarith
