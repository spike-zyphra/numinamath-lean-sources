import Mathlib
open Real Set

/- The solution set of the equation $2\cos \left(x- \frac {\pi}{4}\right)= \sqrt {2}$ in the interval $(0,\pi)$ is \_\_\_\_\_\_. -/
theorem algebra_9363 {x : ℝ} (hx : x ∈ Ioo 0 π) :
    2 * cos (x - π / 4) = √2 ↔ x = π / 2 := by
  -- Split the problem into two goals
  constructor <;> intro h

  . -- x = π / 2 ↔ x - π / 4 = π / 4
    suffices _ : x - π / 4 = π / 4 by linarith
    -- x - π / 4 ∈ (-π / 4, 3 * π / 4)
    have ⟨h1, h2⟩ : x - π / 4 ∈ Ioo (-π / 4) (3 * π / 4) := by
      simp at *
      constructor <;> linarith
    -- Change the variable to y = x - π / 4
    generalize x - π / 4 = y at *
    clear x hx
    -- We need to y = π / 4 from cos y = cos (π / 4)
    replace h : cos y = cos (π / 4) := by linarith [cos_pi_div_four]

    -- Use the lemma cos_eq_cos_iff
    -- cos y = cos (π / 4) ↔ y = π / 4 + 2 * π * k ∨ y = -π / 4 + 2 * π * k, where k is an integer
    obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.1 h
    . -- First case: y = π / 4 + 2 * π * k
      -- -1 < k < 1 from the interval of y
      have hk1 : (k : ℝ) > (-1 : ℤ) := by rw [(by simp : (-1 : ℤ) = (-1 : ℝ))]; nlinarith
      have hk2 : (k : ℝ) < (1 : ℤ) := by rw [(by simp : (1 : ℤ) = (1 : ℝ))]; nlinarith
      -- Thus we get k = 0
      apply Int.cast_lt.1 at hk1
      apply Int.cast_lt.1 at hk2
      interval_cases k
      simp at *
      linarith
    . -- Second case: y = -π / 4 + 2 * π * k
      -- 0 < k < 1 from the interval of y
      have hk1 : (k : ℝ) > (0 : ℤ) := by rw [(by simp : (0 : ℤ) = (0 : ℝ))]; nlinarith
      have hk2 : (k : ℝ) < (1 : ℤ) := by rw [(by simp : (1 : ℤ) = (1 : ℝ))]; nlinarith
      -- No cases for k
      apply Int.cast_lt.1 at hk1
      apply Int.cast_lt.1 at hk2
      interval_cases k

  . -- Plug in x = π / 2 to the equation
    subst h
    simp [(by ring : π / 2 - π / 4 = π / 4)]
    ring
