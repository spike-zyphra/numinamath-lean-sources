import Mathlib

/- 262. Integer solutions are sought. Find all integer solutions of the
equation
$$
y^{2}+y=x^{4}+x^{3}+x^{2}+x
$$
 -/
theorem number_theory_270930 (x y : ℤ) :
    y^2 + y = x^4 + x^3 + x^2 + x ↔
    (x = -1 ∧ y = -1) ∨ (x = -1 ∧ y = 0) ∨
    (x = 0 ∧ y = -1) ∨ (x = 0 ∧ y = 0) ∨
    (x = 2 ∧ y = -6) ∨ (x = 2 ∧ y = 5) := by
  constructor
  -- First show the 6 solutions satisfy the equation
  case mpr => rintro ( _ | _ | _ | _ | _ | _ ) <;> simp_all
  intro eq
  -- Arrange terms with y such that they form a perfect square
  replace eq : (2 * y + 1)^2 = 4*x^4 + 4*x^3 + 4*x^2 + 4*x + 1
      := by
    ring_nf
    rw [show 1 + y * 4 + y ^ 2 * 4 = 1 + 4 * (y^2 + y) by ring, eq]
    ring
  -- Consider either case of x < 2
  obtain (_ | abs_lt) := Classical.em (|x| ≤ 2)
  -- Eliminate the x < 2 case by showing solutions or contradictions
  case inl solutions_range =>
    rw [abs_le, <- Finset.mem_Icc] at solutions_range
    -- Solve the cases where x is a solution first
    fin_cases solutions_range <;> simp_all <;> try omega
    case «4» =>
      rw [show (121 : ℤ) = 11^2 by rfl] at eq
      rw [sq_eq_sq_iff_eq_or_eq_neg] at eq
      omega
    -- Show the rest lead to contradictions
    all_goals
      rw [<- sq_abs, Int.abs_eq_natAbs] at eq
      norm_cast at eq
      have := Nat.not_exists_sq'
        (show 6^2 < 41 by linarith)
        (show 41 < 7^2 by linarith)
      have := Nat.not_exists_sq'
        (show 4^2 < 17 by linarith)
        (show 17 < 5^2 by linarith)
      simp_all
  -- Show |x| < 2
  simp at abs_lt
  -- Show a lower bound that is a perfect square
  have lower_bound : (2 * x^2 + x)^2 < (2*y + 1)^2 := by
    rw [eq]
    ring_nf
    gcongr
    norm_num [
      eq,
      sq_abs,
      show 1 + x * 4 + x^2 * 4 = (2*x + 1)^2 by ring,
      sq_lt_sq
    ]
    -- Show the inequality holds for each absolute value combination
    cases abs_cases x <;> cases abs_cases (2 * x + 1)
      <;> omega
  -- Show an upper bound that is a perfect square
  have upper_bound : (2*y + 1)^2 < (2 * x^2 + x + 1)^2 := by
    rw [eq]
    ring_nf
    field_simp
    -- Show the inequality holds for each absolute value combination
    have : 0 < x^2 - 2 * x := by
      rcases abs_cases x with (⟨ eq, _ ⟩ | ⟨ eq, _ ⟩)
        <;> rw [eq] at abs_lt
        <;> field_simp [pow_two]
        <;> omega
    omega

  -- Cast 2*x^2 + x to a natural absolute value for Nat.not_exists_sq
  have x_abs : 2*x^2 + x = (2*x^2 + x).natAbs := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by linarith)]
  -- Cast (2 * y + 1)^2 to a natural absolute value for Nat.not_exists_sq
  have y_abs : (2 * y + 1)^2 = ((2 * y + 1)^2).natAbs := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by positivity)]
  rw [x_abs, y_abs] at lower_bound upper_bound
  -- Convert to naturals
  norm_cast at lower_bound upper_bound
  -- Show there are no integers between 2x^2 + x and 2x^2 + x + 1
  have := Nat.not_exists_sq' lower_bound upper_bound
  -- It then follows that there are no integer solutions
  push_neg at this
  specialize this (2 * y + 1).natAbs
  -- Revert to integers after applying Nat.not_exists_sq'
  zify [ <- y_abs, sq_abs] at this
  contradiction