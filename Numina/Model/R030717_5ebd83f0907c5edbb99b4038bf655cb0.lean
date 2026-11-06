import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

theorem algebra_123021
    (a b c d e f A B : ℝ)
    (hA : A ∈ Set.Icc 0 1)
    (hB : B ∈ Set.Icc 0 1)
    (h1 : ∀ x y : ℝ, a * x ^ 2 + b * x * y + c * y ^ 2 = (A * x + (1 - A) * y) ^ 2)
    (h2 : ∀ x y : ℝ, (A * x + (1 - A) * y) * (B * x + (1 - B) * y) =
      d * x ^ 2 + e * x * y + f * y ^ 2) :
    (a ≥ 4 / 9 ∨ b ≥ 4 / 9 ∨ c ≥ 4 / 9) ∧ (d ≥ 4 / 9 ∨ e ≥ 4 / 9 ∨ f ≥ 4 / 9) := by

  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  have eq1 := h1 1 0
  have eq2 := h1 0 1
  have eq3 := h1 1 1
  have eq4 := h2 1 0
  have eq5 := h2 0 1
  have eq6 := h2 1 1

  have ha : a = A ^ 2 := by
    nlinarith
  have hc : c = (1 - A) ^ 2 := by
    nlinarith
  have hb : b = 2 * A * (1 - A) := by
    nlinarith [ha, hc]

  -- For the second identity h2:
  -- x = 1, y = 0:
  -- (A * 1 + (1 - A) * 0) * (B * 1 + (1 - B) * 0) = A * B
  -- d * 1 + e * 0 + f * 0 = d
  -- So d = A * B
  have hd : d = A * B := by
    nlinarith
  -- x = 0, y = 1:
  -- (A * 0 + (1 - A) * 1) * (B * 0 + (1 - B) * 1) = (1 - A) * (1 - B)
  -- d * 0 + e * 0 + f * 1 = f
  -- So f = (1 - A) * (1 - B)
  have hf : f = (1 - A) * (1 - B) := by
    nlinarith
  -- x = 1, y = 1:
  -- (A + (1 - A))(B + (1 - B)) = 1 * 1 = 1
  -- d + e + f = 1
  -- e = 1 - (d + f)
  -- e = 1 - (A * B + (1 - A) * (1 - B))
  have he : e = A + B - 2 * A * B := by
    nlinarith [hd, hf]

  constructor
  · -- Show that at least one of a, b, c ≥ 4/9
    by_contra h
    push_neg at h
    rcases h with ⟨ha1, hb1, hc1⟩
    nlinarith [sq_nonneg (A - 1 / 3), sq_nonneg (A - 2 / 3)]
  · -- Show that at least one of d, e, f ≥ 4/9
    by_contra h
    push_neg at h
    rcases h with ⟨hd1, he1, hf1⟩
    nlinarith [sq_nonneg (A - 1 / 3), sq_nonneg (A - 2 / 3), sq_nonneg (B - 1 / 3), sq_nonneg (B - 2 / 3), mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hA2), mul_nonneg (sub_nonneg.mpr hB1) (sub_nonneg.mpr hB2)]