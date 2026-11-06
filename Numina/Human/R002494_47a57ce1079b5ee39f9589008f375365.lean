import Mathlib.Tactic.Linarith

theorem algebra_737 :
    -- Let $b, r + r', w + w'$ be the amount of blue, red and white paints used, respectively.
    -- Here, r' and w' are the amount of red and white paints used to make pink paint.
    ∀ b r r' w w' : ℚ, (
    -- Used paint amounts cannot be negative.
    0 ≤ b ∧ 0 ≤ r ∧ 0 ≤ r' ∧ 0 ≤ w ∧ 0 ≤ w' ∧
    -- We can not use more paint then avaliable.
    b ≤ 130 ∧ r + r' ≤ 164 ∧ w + w' ≤ 188 ∧
    -- From each bucket, an equal amount of paint is used.
    b = r ∧ b = w ∧ b = r' + w' ∧
    -- The remaining paints in the buckets are of equal amount.
    130 - b = 164 - (r + r') ∧ 130 - b = 188 - (w + w')) →
    -- Then the amount of total remaining paint is 114.
    3 * (130 - b) = 114 := by
  intro b r r' w w' h
  -- It follows from simple algebra.
  nlinarith