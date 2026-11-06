import Mathlib

/- Find the minimum value of
\[(12 - x)(10 - x)(12 + x)(10 + x).\] -/
theorem algebra_14879 :
  IsLeast {y : ℝ | ∃ x, y = (12 - x) * (10 - x) * (12 + x) * (10 + x)} (-484) := by
  -- expand (12-x)(10-x)(12+x)(10+x)
  -- notice that (a-b)(a+b) = a^2-b^2, so bundle (12-x)(12+x) together, and (10-x)(10+x) together
  have h1: ∀x:ℝ,(12-x)*(10-x)*(12+x)*(10+x) = (100-x^2) * (144-x^2) := by
    intro x
    have ht1: (12-x)*(10-x)*(12+x)*(10+x) =
      ((10-x)*(10+x)) * ((12-x)*(12+x)) := by ring
    have ht2: (12-x)*(12+x) = (144-x^2) := by ring
    have ht3: (10-x)*(10+x) = 100-x^2 := by ring
    rw [ht1, ht2, ht3]
  -- expand (100-x^2)(144-x^2)
  have h2: ∀x:ℝ, (100-x^2)*(144-x^2) = (x^2)^2 - 244*x^2 + 100*144 := by
    intro x; ring
  -- (x^2)^2 - 244x^2 + 122^2 = (x^2-122)^2
  have h3: ∀x:ℝ, (x^2)^2-244*x^2+100*144 =
    (x^2-122)^2 + (100*144 - 122^2) := by
    intro x; ring
  -- 100*144-122^2 = 100x122+100x22-122x122 = 122x(100-122) + 100x22 = 22x(100-122) = -22^2 = -484
  have h4: (100:ℝ)*144-122^2 = -484 := by ring
  -- so we can prove minimum value is -484, reach minimum when (x^2-122)^2=0, or x = √122 or -√122
  rw [IsLeast, lowerBounds]; simp
  constructor
  · use √122
    have ht1: (√122)^2 = 122 := by field_simp
    have ht2: (√122)^4 = ((√122)^2)^2 := by ring
    ring_nf; simp [ht1, ht2]; ring
  · intro x
    have ht1 := h1 x
    have ht2 := h2 x
    have ht3 := h3 x
    have ht4 := sq_nonneg (x^2 - 122)
    rw [ht1, ht2, ht3, h4]
    linarith [ht4]