import Mathlib

set_option maxHeartbeats 500000

theorem number_theory_607806 :
    {n : ℕ | ∃ a b c d e f g: ℕ, (a = 5 ∨ a = 7) ∧ (b = 5 ∨ b = 7) ∧ (c = 5 ∨ c = 7) ∧ (d = 5 ∨ d = 7) ∧
    (e = 5 ∨ e = 7) ∧ (f = 5 ∨ f = 7) ∧ (g = 5 ∨ g = 7)
    ∧ n = a * 10^6 + b * 10^5 + c * 10^4 + d * 10^3 + e * 10^2 + f * 10 + g ∧ n % 5 = 0 ∧ n % 7 = 0} =
        {7775775, 7757575, 5577775, 7575575, 5777555, 7755755, 5755575, 5557755, 7555555} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in left side.
    rintro ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, hn0, hn1, hn2⟩
    rcases ha with (rfl | rfl)
    <;> rcases hb with (rfl | rfl)
    <;> rcases hc with (rfl | rfl)
    <;> rcases hd with (rfl | rfl)
    <;> rcases he with (rfl | rfl)
    <;> rcases hf with (rfl | rfl)
    <;> rcases hg with (rfl | rfl)
    <;> omega
  · -- Assume n is in right side.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- 7775775
      use 7, 7, 7, 5, 7, 7, 5
      native_decide
    · -- 7757575
      use 7, 7, 5, 7, 5, 7, 5
      native_decide
    · -- 5577775
      use 5, 5, 7, 7, 7, 7, 5
      native_decide
    · -- 7575575
      use 7, 5, 7, 5, 5, 7, 5
      native_decide
    · -- 5777555
      use 5, 7, 7, 7, 5, 5, 5
      native_decide
    · -- 7755755
      use 7, 7, 5, 5, 7, 5, 5
      native_decide
    · -- 5755575
      use 5, 7, 5, 5, 5, 7, 5
      native_decide
    · -- 5557755
      use 5, 5, 5, 7, 7, 5, 5
      native_decide
    · -- 7555555
      use 7, 5, 5, 5, 5, 5, 5
      native_decide