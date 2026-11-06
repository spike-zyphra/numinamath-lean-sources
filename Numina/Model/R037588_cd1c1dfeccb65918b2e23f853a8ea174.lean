import Mathlib

theorem algebra_259240 :
  {n : ℤ | ∃ a b, a * b = n ∧ a - b = 6 ∧ a^4 + b^4 = 272} = {-8} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, so there are a,b such that a * b = n, a - b = 6, a^4 + b^4 = 272.
    rintro ⟨a, b, h1, h2, h3⟩
    have h4 : a = b + 6 := by
      omega
    rw [h4] at h1 h3
    have h7 : (b + 4) * (b + 2) = 0 := by
      nlinarith [sq_nonneg (b^2 + 6 * b + 16), sq_nonneg (b + 4), sq_nonneg (b + 2),
        sq_nonneg ((b + 4) * (b + 2)), sq_nonneg ((b + 4) - (b + 2))]
    have h8 : b + 4 = 0 ∨ b + 2 = 0 := by
      cases (mul_eq_zero.mp h7) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        right
        linarith
    cases h8 with
    | inl h11 =>
      have hb1 : b = -4 := by 
        linarith
      have ha1 : a = 2 := by 
        rw [hb1] at h4 
        omega 
      nlinarith 
    | inr h12 =>
      have hb2 : b = -2 := by 
        linarith
      have ha2 : a = 4 := by 
        rw [hb2] at h4 
        omega 
      nlinarith 
  · -- Assume n = -8 in the right side. We need to show existence.
    intro h
    rw [h]
    use 2, -4 
    all_goals norm_num