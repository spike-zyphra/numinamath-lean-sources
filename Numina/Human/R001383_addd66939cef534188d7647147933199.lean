import Mathlib

theorem Combinatorics_5659
    (S : Finset (ℤ × ℤ))
    (n : ℤ)
    (h₀ : n > 0)
    (h₁ : ∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = n ∧ (x, y) ∈ S)
    (h₂ : ∀ x y : ℤ, (x, y) ∈ S ↔ x^3 - 3 * x * y^2 + y^3 = n) :
    2 < S.card  ∧ ¬ ∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = 2891 := by
  apply And.intro
  · obtain ⟨x, y, h₄, h₅⟩ := h₁
    apply Finset.two_lt_card_iff.mpr
    use (x, y), (y - x, -x), (-y, x - y)
    refine ⟨h₅, ?_, ?_, ?_, ?_, ?_ ⟩
      -- verifying that the solutions are in S
    · rw [h₂, ← h₄]
      ring
      -- verifying that the solutions are in S
    · rw [h₂, ← h₄]
      ring
      --show three solutions are unique
    · simp
      intros tmp tmp1
      simp [tmp1] at *
      nlinarith
    · --show three solutions are unique
      simp
      intros tmp tmp1
      simp [tmp] at *
      nlinarith
    · --show three solutions are unique
      simp
      intros tmp tmp1
      replace tmp : y = 0 := by linarith
      replace tmp1 : x = 0 := by linarith
      rw [tmp, tmp1] at h₄
      simp_all
  · rintro ⟨x, y, h⟩
    -- reduce 2891 to mod 9 using a brute-force check (ZMod 9 is finite)
    have hmod : (x^3 - 3 * x * y^2 + y^3 : ZMod 9) = 2 := by
      norm_cast
      simp [h]
      decide
    -- Show that f_mod x y ≠ 2 for all x y : ZMod 9
    have f_mod_ne_2 : ∀ x y : ZMod 9, x^3 - 3 * x * y^2 + y^3 ≠ 2 := by decide
    --derive a contradiction
    exact f_mod_ne_2 (↑x) (↑y) hmod