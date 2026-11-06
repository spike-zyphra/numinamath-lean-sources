import Mathlib

theorem algebra_292869 (f : ℝ → ℝ) :
    (∀ x y, f (x * f y) + x = f x * f (y + 1)) ↔
    (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
  constructor
  · -- Assume f satisfies the equation, prove it's either identity or negation
    intro h_eq
    have h_eq1 : ∀ y, f 0 = f 0 * f (y + 1) := by
      intro y
      specialize h_eq 0 y
      simp at h_eq ⊢
      linarith
    have h2 : f 0 = 0 ∨ ∀ y, f (y + 1) = 1 := by
      by_cases h : f 0 = 0
      · exact Or.inl h
      · push_neg at h
        right
        intro y
        have : f 0 = f 0 * f (y + 1) := h_eq1 y
        have h' : f 0 ≠ 0 := h
        have : f (y + 1) = 1 := by 
          apply (mul_left_inj' h').mp 
          linarith 
        simpa using this 
    cases h2 with
    | inl h0 =>
      have h_eq4 : ∀ x, f x * f 1 = x := by 
        intro x
        specialize h_eq x 0 
        simp [h0] at h_eq 
        nlinarith 
      have h_eq5 : f 1 ^ 2 = 1 := by 
        specialize h_eq4 1 
        nlinarith 
      have h_eq6 : f 1 = 1 ∨ f 1 = -1 := by 
        rw [sq_eq_one_iff] at h_eq5 
        exact h_eq5 
      cases h_eq6 with
      | inl h_eq1 => 
        have h_f_x : ∀ x, f x = x := by 
          intro x 
          specialize h_eq4 x 
          rw [show f 1 = 1 by linarith [h_eq1] ] at h_eq4
          nlinarith 
        left
        exact h_f_x 
      | inr h_eq1 => 
        have h_f_x : ∀ x, f x = -x := by 
          intro x 
          specialize h_eq4 x 
          rw [show f 1 = -1 by linarith [h_eq1] ] at h_eq4 
          nlinarith 
        right
        exact h_f_x 
    | inr h1_const => 
      have h_f_const : ∀ y, f y = 1 := by 
        intro y 
        have h' := h1_const (y - 1)
        rw [show y - 1 + 1 = y by ring] at h' 
        linarith 
      have h_eq3 : ∀ y, f y = 1 := h_f_const 
      have h_eq' := h_eq 1 0 
      simp [show f 0 = 1 by apply h_eq3, show f 1 = 1 by apply h_eq3, show f (0 + 1) = 1 by apply h_eq3] at h_eq' 
      all_goals linarith 
  · -- Assume f is either identity or negation, prove it satisfies the equation
    rintro (h | h)
    · intro x y 
      simp [h, mul_add, mul_assoc] 
      <;> ring_nf <;> simp [h] <;> ring 
    · intro x y 
      simp [h, mul_add, mul_neg, mul_assoc, add_mul, mul_comm, mul_assoc] 
      <;> ring_nf <;> simp [h] <;> ring 
      <;> norm_num
      <;> ring 
      <;> norm_num
      <;> ring
      all_goals 
      simp [h]
      <;> ring 
      <;> simp [h]
      <;> ring