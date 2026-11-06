import Mathlib

/- 2. (2006 Thailand Mathematical Olympiad) Find all integers $n$, such that $n^{2}+59 n+881$ is a perfect square. -/
theorem number_theory_268866 (n : ℤ) :
  IsSquare (n^2 + 59 * n + 881) ↔ n = -40 ∨ n = -19 := by
  constructor
  -- One direction is trivial
  swap
  · rintro (rfl | rfl); all_goals exact ⟨11, by norm_num⟩
  intro ⟨m, hm⟩
  -- Factorise the equation
  have hf : (2 * m + 2 * n + 59) * (2 * m - 2 * n - 59) = 43
  · trans 4 * (m * m) - (2 * n + 59)^2; ring; rw [←hm]; ring
  -- 43 is prime, so one factor is ±1 and the other is ±43
  have hp' : Prime ((2 * m + 2 * n + 59) * (2 * m - 2 * n - 59))
  · rw [hf]; norm_num
  rcases prime_mul_iff.mp hp' with ⟨hp, hu⟩ | ⟨hu, hp⟩
  · rcases Int.isUnit_iff.mp hu with hpos | hneg
    · rw [hpos, mul_one] at hf; right; linarith [hf, hpos]
    · rw [hneg, mul_neg_one] at hf; left; linarith [hf, hneg]
  rcases Int.isUnit_iff.mp hu with hpos | hneg
  · rw [hpos, one_mul] at hf; left; linarith [hf, hpos]
  rw [hneg, neg_one_mul] at hf; right; linarith [hf, hneg]