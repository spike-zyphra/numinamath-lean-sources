import Mathlib

theorem algebra_18535 :
    ∑ᶠ a ∈ {a : ℝ | ∃! x : ℝ, x ^ 2 + a = a * x}, a = 4 := by
  have h1 : {a : ℝ | ∃! x : ℝ, x ^ 2 + a = a * x} = {0, 4} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume there exists a unique real x such that x² + a = a·x
      intro h
      rcases h with ⟨x, ⟨hx1, hx2⟩⟩
      have h_eq : x ^ 2 + a = a * x := hx1
      have h_eq2 : (a - x) ^ 2 + a = a * (a - x) := by
        nlinarith [h_eq]
      have h_eq3 : a - x = x := by 
        apply hx2 (a - x)
        linarith [h_eq2]
      have ha1 : a = 2 * x := by linarith
      have h_eq4 : x ^ 2 + 2 * x = 2 * x ^ 2 := by
        rw [show a = 2 * x by linarith] at h_eq
        linarith
      have h_eq5 : x * (x - 2) = 0 := by
        linarith [h_eq4]
      cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
      · -- x = 0
        have ha0 : a = 0 := by
          rw [show x = (0 : ℝ) by linarith] at ha1
          linarith
        left
        linarith [ha0]
      · -- x - 2 = 0
        have h_eq7' : x = (2 : ℝ) := by linarith
        have ha4 : a = (4 : ℝ) := by
          rw [show x = (2 : ℝ) by linarith] at ha1
          linarith
        right
        linarith [ha4]
    · -- Assume a is 0 or 4
      rintro (rfl | rfl)
      · -- a = 0
        use (0 : ℝ)
        constructor
        · -- Show that 0^2 + 0 = 0 * 0
          norm_num
        · -- Show that the solution is unique
          intro y hy
          have : y ^ 2 + (0 : ℝ) = (0 : ℝ) * y := by linarith [hy]
          have : y ^ 2 = 0 := by linarith
          have : y = (0 : ℝ) := by nlinarith
          norm_num at this ⊢
          all_goals linarith
      · -- a = 4
        use (2 : ℝ)
        constructor
        · -- Show that 2^2 + 4 = 4 * 2
          norm_num
        · -- Show that the solution is unique
          intro y hy
          have : y ^ 2 + (4 : ℝ) = (4 : ℝ) * y := by linarith [hy]
          have : (y - 2) ^ 2 = 0 := by nlinarith
          have : y = (2 : ℝ) := by nlinarith
          norm_num at this ⊢
          all_goals linarith
  rw [h1]
  rw [show ∑ᶠ (a : ℝ) (_ : a ∈ ({0, 4} : Set ℝ)), a = (0 + 4 : ℝ) by
    rw [finsum_mem_pair (by norm_num)]
    all_goals norm_num
  ]
  all_goals norm_num