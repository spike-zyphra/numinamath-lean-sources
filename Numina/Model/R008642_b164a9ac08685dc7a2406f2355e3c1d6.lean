import Mathlib

theorem algebra_11946 : IsGreatest {c : ℝ | 1 ∈ Set.range (fun x : ℝ => x ^ 2 - 5 * x + c)} (29 / 4) := by
  constructor

  · -- Show that 29/4 is indeed in the set (i.e., 1 is in the range of f when c = 29/4)
    use 5 / 2
    norm_num

  · -- Show that for any c in the set, c ≤ 29/4
    intro c hc
    have h1 : ∃ x : ℝ, x ^ 2 - 5 * x + c = 1 := by
      simpa using hc
    rcases h1 with ⟨x, hx⟩

    have h3 : 29 / 4 - c ≥ 0 := by
      nlinarith [sq_nonneg (x - 5 / 2)]

    linarith