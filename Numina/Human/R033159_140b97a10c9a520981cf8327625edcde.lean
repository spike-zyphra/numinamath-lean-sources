import Mathlib

/- Show that $\sqrt{2}+\sqrt{3}$ is irrational. -/
theorem number_theory_114397 : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  -- prove by contradiction, assume √2 + √3 is rational
  dsimp [Irrational]
  by_contra h
  obtain ⟨x, hx⟩ := h
  -- square to obtain 5 + 2√6
  have hx' : x^2 = (√2 + √3)^2 := by rw [hx]
  ring_nf at hx'
  simp at hx'
  have : √2 * √3 = √(2 * 3) := by
    refine (Real.sqrt_mul ?_ ?_).symm
    all_goals simp
  rw [this] at hx'
  ring_nf at hx'
  -- that means √6 is rational
  have : √6 = (x^2 - 5)/2 := by linarith
  have : √6 = (((x^2-5)/2):ℚ) := by exact_mod_cast this
  have : √6 ∈ Set.range Rat.cast := by
    use (x^2-5)/2
    rw [this]
  -- but √6 is irratinal, as 6 is not a square, prove by trying out 1 to 6 as root
  have : Irrational √6 := by
    convert_to Irrational √(6:ℕ)
    rw [irrational_sqrt_natCast_iff]
    dsimp [IsSquare]
    by_contra h
    obtain ⟨r, hr⟩ := h
    have : r ≤ 6 := by calc
      r ≤ r^2 := by exact Nat.le_self_pow (by simp: 2 ≠ 0) r
      _ = 6 := by rw [hr]; ring
    interval_cases r
    all_goals linarith
  contradiction