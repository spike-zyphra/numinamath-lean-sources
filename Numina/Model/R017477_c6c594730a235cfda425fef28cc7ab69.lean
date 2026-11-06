import Mathlib

theorem algebra_165166 (a : ℝ) (M : Set ℝ) (hM : M = {x | x^3 + (a^2 + 1)*x + 2*a^2 + 10 = 0}) :
    {S | S ⊆ M ∧ S.Nonempty}.ncard = 1 := by
  have h1 : M = {-2} := by
    ext x
    simp [hM]
    constructor
    · -- Assume h
      intro h
      have h_eq : x^3 + (a^2 + 1)*x + 2*a^2 + 10 = 0 := by
        simpa using h
      have h2 : (x + 2) * (x^2 - 2 * x + (a^2 + 5)) = 0 := by
        nlinarith [h_eq, sq_nonneg (x - 1), sq_nonneg (a + 2), sq_nonneg (x - (1 - a)), sq_nonneg (x - (1 + a)), sq_nonneg (x - 2)]
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case x + 2 = 0, so x = -2
        linarith
      · -- Case x^2 - 2 x + a^2 + 5 = 0
        have h5 : (x - 1)^2 + (a^2 + 4) = 0 := by
          nlinarith
        have h6 : (x - 1)^2 ≥ 0 := by
          apply sq_nonneg
        nlinarith [sq_nonneg a]
    · -- Assume x = -2
      intro h
      rw [h]
      have h2 : a^2 ≥ 0 := by apply sq_nonneg
      nlinarith
  have h2 : {S | S ⊆ M ∧ S.Nonempty} = {({-2} : Set ℝ)} := by
    ext S
    simp only [h1, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume S ⊆ {-2} and S is non-empty
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : S = {-2} := by
        have h4 : ∀ x : ℝ, x ∈ S → x = -2 := by
          intro x hx
          have hxS : x ∈ ({-2} : Set ℝ) := by
            apply h1 hx
          simpa using hxS
        have h5 : S.Nonempty := h2
        rcases h5 with ⟨x, hx⟩
        have hx2 : x = -2 := h4 x hx
        ext y
        simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
        constructor
        · -- Assume y ∈ S
          intro h6
          have h7 : y = -2 := h4 y h6
          tauto
        · -- Assume y = -2
          intro h6
          rw [h6]
          have h7 : (-2 : ℝ) ∈ S := by
            have h7 : x = -2 := hx2
            rw [show x = -2 from hx2] at hx
            tauto
          exact h7
      simp [h3]
    · -- Assume S = {-2}, need to show is subset and non-empty
      intro h
      rw [h]
      constructor
      · -- Show that every element in {-2} is in M
        simp [h1]
      · -- Show that {-2} is non-empty
        simp
  rw [h2]
  simp