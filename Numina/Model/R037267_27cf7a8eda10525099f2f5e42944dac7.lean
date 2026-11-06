import Mathlib

theorem algebra_187281 :
    Set.encard {m : ℤ | ∃ α : ℝ, -1988 ≤ α ∧ α ≤ 1988 ∧ 6 * α ^ 2 = (2 * m - 1) * α + m + 1 ∧
      ∃ k : ℤ, 3 / 5 * α = k} = 2385 := by
  have h1 : {m : ℤ | ∃ α : ℝ, -1988 ≤ α ∧ α ≤ 1988 ∧ 6 * α ^ 2 = (2 * m - 1) * α + m + 1 ∧
      ∃ k : ℤ, 3 / 5 * α = k} = Finset.image (fun (k : ℤ) => 5 * k - 1) (Finset.Icc (-1192) 1192) := by
    ext m
    simp
    constructor
    · -- Assume h exists.
      intro h
      rcases h with ⟨α, h1, h2, heq, k, hk⟩
      have h_eq1 : 6 * α ^ 2 - (2 * (m : ℝ) - 1) * α - (m + 1 : ℝ) = (0 : ℝ) := by
        linarith
      have h_eq2 : (α - ((m + 1) / 3 : ℝ)) * (α + (1 / 2 : ℝ)) = 0 := by
        nlinarith
        <;> ring_nf
        <;> nlinarith
      cases (mul_eq_zero.mp h_eq2) with
      | inl h_eq3 =>
        have h_eq4 : α = ((m + 1) / (3 : ℝ)) := by
          linarith
        have eq2 : (k : ℝ) = (m + 1) / (5 : ℝ) := by
          rw [h_eq4] at hk
          have eq1 : (3 / 5 * ((m + 1 : ℝ) / 3) ) = (k : ℝ) := by linarith
          have eq2 : (k : ℝ) = (3 / 5 * ((m + 1 : ℝ) / 3) ) := by linarith
          field_simp at eq2 ⊢
          nlinarith
          all_goals nlinarith
        have eq3 : (k * 5 : ℝ) = (m + 1 : ℝ) := by
          nlinarith
        have eq4 : k * 5 = m + 1 := by
          exact_mod_cast eq3
        have eq5 : m = 5 * k - 1 := by
          omega
        have h_m1 : -1988 ≤ (α : ℝ) := h1
        rw [h_eq4] at h_m1
        have h_m1' : -5964 ≤ m + 1 := by
          by_contra h
          push_neg at h
          have h_m10 : (m + 1 : ℝ) < (-5964 : ℝ) := by
            exact_mod_cast h
          nlinarith
        have h_m2 : (α : ℝ) ≤ 1988 := h2
        rw [h_eq4] at h_m2
        have h_m2' : (m + 1 : ℝ) ≤ 5964 := by
          nlinarith
        have h_m2'' : m + 1 ≤ 5964 := by
          exact_mod_cast h_m2'
        have h_k1 : k ≥ -1192 := by
          by_contra h
          push_neg at h
          have hk5 : k ≤ -1193 := by omega
          have hk6 : k * 5 ≤ -5965 := by
            nlinarith
          have hk7 : m + 1 ≤ -5965 := by
            omega
          have hk8 : (m + 1 : ℝ) ≤ (-5965 : ℝ) := by
            exact_mod_cast hk7
          nlinarith
          all_goals tauto
          all_goals try { tauto <;> nlinarith <;> omega <;> tauto <;> nlinarith }
        have h_k2 : k ≤ 1192 := by
          by_contra h
          push_neg at h
          have hk5 : k ≥ 1193 := by omega
          have hk6 : k * 5 ≥ 5965 := by
            nlinarith
          have hk7 : m + 1 ≥ 5965 := by
            omega
          have hk8 : (m + 1 : ℝ) ≥ (5965 : ℝ) := by
            exact_mod_cast hk7
          nlinarith
          all_goals tauto
          all_goals try { tauto <;> nlinarith <;> omega }
        rw [eq5]
        simp [Finset.mem_image, Finset.mem_Icc]
        tauto
        all_goals try { tauto <;> nlinarith <;> omega }
      | inr h_eq3 =>
        have h_eq4 : α = (-1 / 2 : ℝ) := by
          linarith
        have h_eq5 : (3 / 5) * (α : ℝ) = (k : ℝ) := by
          linarith
        rw [h_eq4] at h_eq5
        have eq1 : (k : ℝ) = -(3 / 10) := by
          linarith
          <;> norm_num <;> field_simp <;> ring_nf <;> nlinarith
        -- This is a contradiction as k is integer.
        have eq2 : (k : ℝ) * 10 = -3 := by
          nlinarith
        have eq3 : k * 10 = -3 := by
          exact_mod_cast eq2
        -- Impossible.
        omega
        <;> try { tauto <;> nlinarith }
    · -- Assume m in the image.
      rintro ⟨k, ⟨h_k1, h_k2⟩, rfl⟩
      use (5 * (k : ℝ) / 3)
      constructor
      · -- Check -1988 ≤ α
        have h_k1 : (k : ℝ) ≥ -1192 := by exact_mod_cast h_k1
        have h_k2 : (k : ℝ) ≤ (1192 : ℝ) := by exact_mod_cast h_k2
        nlinarith
      constructor
      · -- Check α ≤ 1988
        have h_k1 : (k : ℝ) ≥ -1192 := by exact_mod_cast h_k1
        have h_k2 : (k : ℝ) ≤ (1192 : ℝ) := by exact_mod_cast h_k2
        nlinarith
      constructor
      · -- Check the quadratic.
        have eq2 : 6 * ((5 * (k : ℝ) / 3) ^ 2) = (2 * ((5 * k - 1 : ℤ) : ℝ) - 1) * (5 * (k : ℝ) / 3) + (5 * k - 1 : ℤ) + 1 := by
          ring_nf
          <;> norm_num <;> nlinarith <;> ring_nf <;> norm_num
          <;> field_simp <;> ring_nf <;> norm_num
          all_goals tauto
          <;> try { tauto <;> nlinarith <;> ring }
        norm_num at *
        linarith
        <;> try { tauto <;> ring_nf <;> norm_num <;> linarith <;> tauto }
        all_goals try { tauto <;> nlinarith }
      · -- Check exists integer k.
        use k
        field_simp
        <;> norm_num <;> nlinarith
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide
  <;> try { linarith <;> try { tauto } }