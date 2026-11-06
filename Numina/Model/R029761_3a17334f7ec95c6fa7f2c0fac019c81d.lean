import Mathlib

theorem number_theory_72973 (α : ℝ) (p q : ℤ) (qne0 : q ≠ 0) (hcos : Real.cos α = p / q) (n : ℕ) :
    ∃ m : ℤ, q ^ n * Real.cos (n * α) = m := by 
  have h1 : ∀ (n : ℕ), ∃ m : ℤ, q ^ n * Real.cos (n * α) = m := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use 1 
      simp [hcos]
      <;> ring_nf 
      <;> norm_num 
      <;> field_simp [qne0]
      <;> norm_num 
    | succ n => 
      cases n with
      | zero => 
        use p 
        simp [hcos]
        <;> field_simp [qne0]
        <;> ring 
      | succ n => 
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        simp [show n + 1 ≤ n + 2 by omega] at h2 
        simp [show n ≤ n + 2 by omega] at h3 
        rcases h2 with ⟨m, hm⟩
        rcases h3 with ⟨k, hk⟩
        have hcos_add : Real.cos ((n + 2) * α) = 2 * Real.cos α * Real.cos ((n + 1) * α) - Real.cos (n * α) := by 
          have h1 : Real.cos ((n + 2) * α) = Real.cos ((n + 1) * α + α) := by 
            ring_nf 
          rw [h1]
          have h1a : Real.cos ((n + 1) * α + α) = Real.cos ((n + 1) * α) * Real.cos α - Real.sin ((n + 1) * α) * Real.sin α := by 
            rw [Real.cos_add]
          rw [h1a]
          have h4 : Real.cos (n * α) = Real.cos ((n + 1) * α - α) := by 
            ring_nf 
          rw [h4]
          have h5 : Real.cos ((n + 1) * α - α) = Real.cos ((n + 1) * α) * Real.cos α + Real.sin ((n + 1) * α) * Real.sin α := by 
            rw [Real.cos_sub]
          rw [h5]
          -- Simplify using trigonometric identities
          ring_nf 
          <;> simp [Real.sin_sq, Real.cos_sq] 
          <;> ring_nf 
          <;> norm_num 
          <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq ((n + 1) * α)]
          <;> norm_num 
          <;> ring_nf
          <;> norm_num 
        use 2 * p * m - q ^ 2 * k 
        have h5 : Real.cos ((n + 1) * α) = (m : ℝ) / (q ^ (n + 1) : ℝ) := by 
          have h_eq : (q : ℝ) ^ (n + 1) * Real.cos ((n + 1) * α) = (m : ℝ) := by 
            linarith 
          field_simp at h_eq ⊢ 
          linarith 
        have h6 : Real.cos (n * α) = (k : ℝ) / (q ^ (n : ℕ) : ℝ) := by 
          have h_eq : (q : ℝ) ^ (n : ℕ) * Real.cos (n * α) = (k : ℝ) := by 
            linarith 
          field_simp at h_eq ⊢ 
          linarith 
        have h7 : Real.cos α = (p : ℝ) / (q : ℝ) := by 
          exact_mod_cast hcos 
        have h8 : Real.cos ((n + 2) * α) = (2 * p * m - q ^ 2 * k) / (q ^ (n + 2) : ℝ) := by 
          rw [hcos_add]
          rw [h5, h6, h7]
          field_simp 
          <;> ring_nf 
          <;> field_simp 
          <;> ring 
        have h9 : (q : ℝ) ^ (n + 2) * Real.cos ((n + 2) * α) = (2 * p * m - q ^ 2 * k : ℝ) := by 
          rw [h8] 
          <;> field_simp 
          <;> ring 
        exact_mod_cast h9 
  obtain ⟨m, hm⟩ := h1 n 
  exact ⟨m, by linarith⟩ 
  all_goals 
    ring_nf 
    <;> norm_num 
    <;> try { tauto } 
    <;> try { nlinarith } 
    <;> try { ring } 
    <;> try { norm_num }
    <;> try { tauto }
    <;> try { nlinarith }