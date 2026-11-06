import Mathlib

theorem algebra_164561 {a : ℝ} (ha : a ≠ 0) (h : ∃ m : ℤ, a + 1 / a = m) (n : ℕ) :
    ∃ p : ℤ, a ^ n + 1 / a ^ n = p := by
  rcases h with ⟨m, hm⟩
  have h1 : ∀ n : ℕ, ∃ p : ℤ, a ^ n + 1 / a ^ n = p := by
    intro n 
    induction' n using Nat.twoStepInduction with n ih1 ih2 
    · -- Base case n = 0: $a^0 + 1/a^0 = 2$ (as $a^0 = 1$)
      use 2
      field_simp
      <;> norm_num
      <;> ring_nf
      <;> field_simp
      <;> norm_num
    · -- Base case n = 1: $a + 1/a = m$ by assumption
      use m
      field_simp at hm ⊢ 
      <;> norm_num at hm ⊢ 
      all_goals nlinarith 
    · -- Induction step: Assume it holds for $n$ and $n+1$, prove for $n+2$
      rcases ih1 with ⟨p, hp⟩
      rcases ih2 with ⟨q, hq⟩
      use m * q - p 
      have h_eq : a ^ (n + 2) + 1 / a ^ (n + 2) = (a + 1 / a) * (a ^ (n + 1) + 1 / a ^ (n + 1)) - (a ^ n + 1 / a ^ n) := by
        field_simp at *
        ring_nf 
        <;> field_simp
        <;> ring_nf 
        all_goals field_simp [ha]
        all_goals nlinarith 
      rw [h_eq, hm, hq, hp]
      <;> field_simp [ha]
      <;> ring_nf
      <;> field_simp [ha]
      <;> ring_nf 
      <;> norm_cast 
      <;> field_simp [ha]
      <;> ring_nf 
      <;> norm_cast 
      <;> nlinarith 
      all_goals try { field_simp at * <;> ring_nf <;> norm_cast <;> field_simp }
      <;> try { tauto }
      <;> try { nlinarith }
  specialize h1 n
  exact h1