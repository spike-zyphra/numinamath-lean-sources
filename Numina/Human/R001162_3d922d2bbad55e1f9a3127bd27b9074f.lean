import Mathlib

/- How many positive and negative integers is $12$ a multiple of? -/
theorem algebra_20794 : ({x : ℤ | x > 0 ∧ x ∣ 12} ∪ {x : ℤ | x < 0 ∧ x ∣ 12}).encard = 12 := by
  -- We find all the positive and negative integers that are multiples of 12
  suffices H : {x : ℤ | x > 0 ∧ x ∣ 12} = {1, 2, 3, 4, 6, 12} ∧ {x : ℤ | x < 0 ∧ x ∣ 12} = {-1, -2, -3, -4, -6, -12} by
    rcases H with ⟨H1, H2⟩
    -- Count the elements of the set
    rw [H1, H2]
    simp
    -- It is a finite set, so we can use the cardinality
    rw [show ({-1, -2, -3, -4, -6, -12, 1, 2, 3, 4, 6, 12} : Set ℤ) = ({-1, -2, -3, -4, -6, -12, 1, 2, 3, 4, 6, 12} : Finset ℤ) by simp]
    rw [Set.encard_coe_eq_coe_finsetCard]
    simp
  -- We prove the two goals
  constructor
  . -- First, we prove that the positive integers that are multiples of 12 are the set {1, 2, 3, 4, 6, 12}
    ext x
    simp
    constructor
    . rintro ⟨h1, h2⟩
      -- Get x ≤ 12
      have h3 : x ≤ 12 := Int.le_of_dvd (by norm_num) h2
      -- Enumerate all positive integers ≤ 12
      interval_cases x
      all_goals
        clear * - h2
        -- Either x is not a divisor of 12, or it has been listed in the goal
        trivial
    . -- Check all the numbers in the set is a divisor of 12
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        trivial
  . -- Second, we prove that the negative integers that are multiples of 12 are the set {-1, -2, -3, -4, -6, -12}
    ext x
    simp
    constructor
    . rintro ⟨h1, h2⟩
      -- Get x ≥ -12
      have h3 : x ≥ -12 := Int.neg_le_of_neg_le (Int.le_of_dvd (by norm_num) (Int.neg_dvd.2 h2))
      -- Enumerate all negative integers ≥ -12
      interval_cases x
      all_goals
        clear * - h1 h2 h3
        trivial
    . -- Check all the numbers in the set is a divisor of 12
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        trivial
