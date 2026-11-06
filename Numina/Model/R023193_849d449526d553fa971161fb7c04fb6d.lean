import Mathlib

theorem algebra_123904 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 2 * x + 3)
    (a : ℝ) (ha : 0 < a) (hmax : IsGreatest (Set.image f (Set.Icc 0 a)) 3)
    (hmin : IsLeast (Set.image f (Set.Icc 0 a)) 2) :
    1 ≤ a ∧ a ≤ 2 := by

  have h1 : ∀ x, f x = x^2 - 2 * x + 3 := by
    intro x
    rw [hf]

  have h2 : 3 ∈ Set.image f (Set.Icc 0 a) := hmax.1

  rcases h2 with ⟨y, hy, h_eq⟩

  have h3 : 0 ≤ y := by
    have h3 : y ∈ Set.Icc (0 : ℝ) a := hy
    rcases h3 with ⟨h31, h32⟩
    linarith

  have h5 : y ≤ a := by
    have h3 : y ∈ Set.Icc (0 : ℝ) a := hy
    rcases h3 with ⟨h31, h32⟩
    linarith

  have eq1 : f y = 3 := by
    linarith [h_eq]

  rw [h1 y] at eq1

  have h3_eq : y^2 - 2 * y + 3 = 3 := by linarith

  have hy_eq : y * (y - 2) = 0 := by
    nlinarith

  have h4 : 2 ∈ Set.image f (Set.Icc 0 a) := hmin.1

  rcases h4 with ⟨x, hx, h_eq2⟩

  have h5 : 0 ≤ x := by
    have h4 : x ∈ Set.Icc (0 : ℝ) a := hx
    rcases h4 with ⟨h41, h42⟩
    linarith

  have h6 : x ≤ a := by
    have h4 : x ∈ Set.Icc (0 : ℝ) a := hx
    rcases h4 with ⟨h41, h42⟩
    linarith

  have eq2 : f x = 2 := by
    linarith [h_eq2]

  rw [h1 x] at eq2

  have h7_eq : x^2 - 2 * x + 3 = 2 := by linarith

  have hx_eq : x = 1 := by
    nlinarith

  have h6 : 1 ≤ a := by
    nlinarith [hx_eq]

  have h5 : ∀ z, z ∈ Set.image f (Set.Icc 0 a) → z ≤ 3 := by
    apply hmax.2

  have h5' : a ∈ Set.Icc (0 : ℝ) a := by
    constructor
    · -- Show that 0 ≤ a
      linarith
    · -- Show that a ≤ a
      linarith

  have h6 : f a ∈ Set.image f (Set.Icc 0 a) := by
    use a
    all_goals
    try { tauto }

  have h7 : f a ≤ 3 := by
    apply h5 (f a) h6

  have h8 : a^2 - 2 * a + 3 ≤ 3 := by
    have eq2 : f a = a^2 - 2 * a + 3 := by
      rw [h1 a]
    nlinarith [h7, eq2]

  have h10 : a ≤ 2 := by
    nlinarith

  constructor
  · -- Show that 1 ≤ a
    linarith
  · -- Show that a ≤ 2
    linarith