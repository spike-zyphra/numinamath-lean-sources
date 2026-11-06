import Mathlib

theorem algebra_197747 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-11.5) 11.5 ∧ b ∈ Set.Icc (-11.5) 11.5 ∧ c ∈ Set.Icc (-11.5) 11.5 ∧ d ∈ Set.Icc (-11.5) 11.5} 552 := by
  constructor
  · -- Show 552 is achievable with a = c = -11.5 and b = d = 11.5
    use -11.5, 11.5, -11.5, 11.5
    norm_num [Set.mem_Icc]
  · -- Show that 552 is the maximum
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    -- Apply constraints to all variables
    have h1 : -11.5 ≤ a := ha1
    have h2 : a ≤ 11.5 := ha2
    have h3 : -11.5 ≤ b := hb1
    have h4 : b ≤ 11.5 := hb2
    have h5 : -11.5 ≤ c := hc1
    have h6 : c ≤ 11.5 := hc2
    have h7 : -11.5 ≤ d := hd1
    have h8 : d ≤ 11.5 := hd2
    -- Using nonlinear arithmetic solver with constraints
    nlinarith [sq_nonneg (a + 11.5), sq_nonneg (b - 11.5), sq_nonneg (c + 11.5), sq_nonneg (d - 11.5),
      sq_nonneg (a - 11.5), sq_nonneg (b + 11.5), sq_nonneg (c - 11.5), sq_nonneg (d + 11.5)]