import Mathlib

theorem number_theory_16494 : {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ ∃ p q : ℕ, (n / 350 : ℝ) = p / 10 ^ q}.encard = 49 := by 
  have h2 : {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ ∃ p q : ℕ, (n / 350 : ℝ) = p / 10 ^ q} = 
          {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ (7 ∣ n)} := by
    ext n 
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Assume n in the left side 
      rintro ⟨h1, h2, ⟨p, q, heq⟩⟩ 
      have eq1 : (n / (350 : ℝ) ) = (p / (10 : ℝ)^ q) := by 
        simpa using heq
      have eq2 : (n : ℝ) * ( (10 : ℝ) ^ q ) = (350 : ℝ) * (p : ℝ) := by 
        field_simp at eq1 ⊢ 
        nlinarith 
      have eq3 : (n * (10 ^ q)) = (350 * p) := by
        exact_mod_cast eq2
      -- Show 7 divides n
      have eq4 : 7 ∣ n := by 
        have eq5 : n * (10 ^ q) = 350 * p := eq3 
        have eq6 : n * (10 ^ q) = 7 * (50 * p) := by 
          ring_nf 
          all_goals omega 
        have eq7 : 7 ∣ n * (10 ^ q) := by 
          omega 
        have h7 : ¬ (7 ∣ (10 ^ q)) := by 
          intro h 
          have h8 : (7 ∣ 10 ^ q) := by 
            omega 
          have h12 : (10 ^ q) % 7 = 0 := by 
            omega 
          have h13 : (10 ^ q) % 7 = 1 ∨ (10 ^ q) % 7 = 3 ∨ (10 ^ q) % 7 = 2 ∨ (10 ^ q) % 7 = 6 ∨ (10 ^ q) % 7 = 4 ∨ (10 ^ q) % 7 = 5 := by
            have h14 : ∀ (q : ℕ), (10 ^ q : ℕ) % 7 = 1 ∨ (10 ^ q : ℕ) % 7 = 3 ∨ (10 ^ q : ℕ) % 7 = 2 ∨ (10 ^ q : ℕ) % 7 = 6 ∨ (10 ^ q : ℕ) % 7 = 4 ∨ (10 ^ q : ℕ) % 7 = 5 := by
              intro q 
              induction q with 
              | zero => 
                norm_num 
              | succ q ih => 
                simp [pow_succ, Nat.mul_mod] at ih ⊢ 
                omega 
            specialize h14 q 
            assumption 
          omega 
        have h21 : 7 ∣ n := by 
          by_contra h 
          push_neg at h 
          have h25 : ¬ (7 ∣ n) := by 
            omega 
          have h33 : (7 ∣ n * (10 ^ q)) := eq7 
          have h34 : ¬ (7 ∣ n) := h25 
          have h44 : (n * (10 ^ q)) % 7 = 0 := by 
            omega 
          have h66 : (n * (10 ^ q)) % 7 = (n % 7) * ((10 ^ q) % 7) % 7 := by 
            simp [Nat.mul_mod] 
          rw [h66] at h44 
          have h77 : (n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6) := by 
            omega 
          rcases h77 with (h77 | h77 | h77 | h77 | h77 | h77)
          all_goals 
            have eq55 : ( (10 ^ q) % 7 = 1 ∨ (10 ^ q) % 7 = 3 ∨ (10 ^ q) % 7 = 2 ∨ (10 ^ q) % 7 = 6 ∨ (10 ^ q) % 7 = 4 ∨ (10 ^ q) % 7 = 5 ) := by 
              omega 
            have eq56 : ( (10 ^ q) % 7 > 0 ) := by 
              omega 
            simp [h77, eq56] at h44 
            <;> omega 
        assumption 
      omega 
    · -- Assume n in the right side
      rintro ⟨h1, h2, h7⟩ 
      have eq4 : ∃ p q : ℕ, (n / (350 : ℝ) ) = (p / (10 : ℝ)^ q) := by 
        use 2 * (n / 7), 2 
        have h8 : 7 ∣ n := h7 
        rcases h8 with ⟨k, hk⟩ 
        rw [hk] 
        norm_num 
        all_goals 
          field_simp 
          <;> ring_nf 
      tauto 
  rw [h2] 
  have h3 : ({n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ (7 ∣ n)} : Set ℕ) = 
          Finset.filter (fun (n : ℕ) => 1 ≤ n ∧ n ≤ 349 ∧ (7 ∣ n)) (Finset.Icc (0 : ℕ) 349) := by 
    ext n 
    simp 
    <;> omega 
  rw [h3] 
  rw [Set.encard_coe_eq_coe_finsetCard] 
  native_decide