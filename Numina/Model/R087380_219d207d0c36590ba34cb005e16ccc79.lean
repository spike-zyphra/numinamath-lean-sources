import Mathlib

theorem algebra_142316 :
    ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧
      (∃ x1 x2 : ℤ, x1 ≠ 0 ∧ x2 ≠ 0 ∧ a * x1^2 + b * x1 + c = 0 ∧ a * x2^2 + b * x2 + c = 0) ∧
      (∃ x3 x4 : ℤ, x3 ≠ 0 ∧ x4 ≠ 0 ∧ a * x3^2 - b * x3 + c = 0 ∧ a * x4^2 - b * x4 + c = 0) ∧
      (∃ x5 x6 : ℤ, x5 ≠ 0 ∧ x6 ≠ 0 ∧ a * x5^2 + b * x5 - c = 0 ∧ a * x6^2 + b * x6 - c = 0) ∧
      (∃ x7 x8 : ℤ, x7 ≠ 0 ∧ x8 ≠ 0 ∧ a * x7^2 - b * x7 - c = 0 ∧ a * x8^2 - b * x8 - c = 0) := by
  use 1
  use 5
  use 6
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- roots for x^2 +5x +6 =0
    use -2, -3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- verify -2 is a root
      norm_num
    · -- verify -3 is a root
      norm_num
  constructor
  · -- roots for x^2 -5x +6 =0
    use 2, 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- verify 2 is a root
      norm_num
    · -- verify 3 is a root
      norm_num
  constructor
  · -- roots for x^2 +5x -6 =0
    use 1, -6
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- verify 1 is a root
      norm_num
    · -- verify -6 is a root
      norm_num
  · -- roots for x^2 -5x -6 =0
    use 6, -1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- verify 6 is a root
      norm_num
    · -- verify -1 is a root
      norm_num