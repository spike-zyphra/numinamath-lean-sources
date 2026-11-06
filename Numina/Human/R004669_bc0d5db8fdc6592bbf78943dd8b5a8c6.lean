import Mathlib

lemma djs (a b : ℕ) : (|(a : ℤ) - b| ∣ (a + b) ↔ |(a : ℤ) - b| ∣ (2 * a)) ∧ (|(a : ℤ) - b| ∣ (a + b) ↔ |(a : ℤ) - b| ∣ (2 * b)) := by
  have h₁ : (|(a : ℤ) - b| ∣ (a + b : ℤ)) → (|(a : ℤ) - b| ∣ (2 * a : ℤ)) := by
    intro h₁
    have h₂ : (|(a : ℤ) - b| : ℤ) ∣ (a + b : ℤ) := by exact_mod_cast h₁
    have h₃ : (|(a : ℤ) - b| : ℤ) ∣ ((a : ℤ) - b) := by
      apply Int.dvd_of_emod_eq_zero
      simp [Int.emod_emod, Int.emod_eq_zero_of_dvd, Int.emod_self]
    have h₄ : (|(a : ℤ) - b| : ℤ) ∣ (2 * a : ℤ) := by
      have h₅ : (2 * a : ℤ) = (a + b : ℤ) + ((a : ℤ) - b) := by
        ring
      rw [h₅]
      exact dvd_add h₂ h₃
    exact_mod_cast h₄
  
  have h₂ : (|(a : ℤ) - b| ∣ (a + b : ℤ)) → (|(a : ℤ) - b| ∣ (2 * b : ℤ)) := by
    intro h₂
    have h₃ : (|(a : ℤ) - b| : ℤ) ∣ (a + b : ℤ) := by exact_mod_cast h₂
    have h₄ : (|(a : ℤ) - b| : ℤ) ∣ ((a : ℤ) - b) := by
      apply Int.dvd_of_emod_eq_zero
      simp [Int.emod_emod, Int.emod_eq_zero_of_dvd, Int.emod_self]
    have h₅ : (|(a : ℤ) - b| : ℤ) ∣ (2 * b : ℤ) := by
      have h₆ : (2 * b : ℤ) = (a + b : ℤ) - ((a : ℤ) - b) := by
        ring
      rw [h₆]
      exact dvd_sub h₃ h₄
    exact_mod_cast h₅
  
  have h₃ : (|(a : ℤ) - b| ∣ (2 * a : ℤ)) → (|(a : ℤ) - b| ∣ (a + b : ℤ)) := by
    intro h₃
    have h₄ : (|(a : ℤ) - b| : ℤ) ∣ (2 * a : ℤ) := by exact_mod_cast h₃
    have h₅ : (|(a : ℤ) - b| : ℤ) ∣ ((a : ℤ) - b) := by
      apply Int.dvd_of_emod_eq_zero
      simp [Int.emod_emod, Int.emod_eq_zero_of_dvd, Int.emod_self]
    have h₆ : (|(a : ℤ) - b| : ℤ) ∣ (a + b : ℤ) := by
      have h₇ : (a + b : ℤ) = (2 * a : ℤ) - ((a : ℤ) - b) := by
        ring
      rw [h₇]
      exact dvd_sub h₄ h₅
    exact_mod_cast h₆
  
  have h₄ : (|(a : ℤ) - b| ∣ (2 * a : ℤ)) ↔ (|(a : ℤ) - b| ∣ (2 * b : ℤ)) := by
    constructor
    · -- Prove the forward direction: if |a - b| ∣ 2 * a, then |a - b| ∣ 2 * b
      intro h₄
      have h₅ : (|(a : ℤ) - b| : ℤ) ∣ (2 * a : ℤ) := by exact_mod_cast h₄
      have h₆ : (|(a : ℤ) - b| : ℤ) ∣ (2 * b : ℤ) := by
        have h₇ : (2 * b : ℤ) = (2 * a : ℤ) - 2 * ((a : ℤ) - b) := by
          ring
        rw [h₇]
        have h₈ : (|(a : ℤ) - b| : ℤ) ∣ (2 * a : ℤ) := h₅
        have h₉ : (|(a : ℤ) - b| : ℤ) ∣ (2 * ((a : ℤ) - b)) := by
          have h₁₀ : (|(a : ℤ) - b| : ℤ) ∣ ((a : ℤ) - b) := by
            apply Int.dvd_of_emod_eq_zero
            simp [Int.emod_emod, Int.emod_eq_zero_of_dvd, Int.emod_self]
          have h₁₁ : (|(a : ℤ) - b| : ℤ) ∣ (2 * ((a : ℤ) - b)) := by
            exact dvd_mul_of_dvd_right h₁₀ 2
          exact h₁₁
        exact dvd_sub h₈ h₉
      exact_mod_cast h₆
    · -- Prove the reverse direction: if |a - b| ∣ 2 * b, then |a - b| ∣ 2 * a
      intro h₄
      have h₅ : (|(a : ℤ) - b| : ℤ) ∣ (2 * b : ℤ) := by exact_mod_cast h₄
      have h₆ : (|(a : ℤ) - b| : ℤ) ∣ (2 * a : ℤ) := by
        have h₇ : (2 * a : ℤ) = (2 * b : ℤ) + 2 * ((a : ℤ) - b) := by
          ring
        rw [h₇]
        have h₈ : (|(a : ℤ) - b| : ℤ) ∣ (2 * b : ℤ) := h₅
        have h₉ : (|(a : ℤ) - b| : ℤ) ∣ (2 * ((a : ℤ) - b)) := by
          have h₁₀ : (|(a : ℤ) - b| : ℤ) ∣ ((a : ℤ) - b) := by
            apply Int.dvd_of_emod_eq_zero
            simp [Int.emod_emod, Int.emod_eq_zero_of_dvd, Int.emod_self]
          have h₁₁ : (|(a : ℤ) - b| : ℤ) ∣ (2 * ((a : ℤ) - b)) := by
            exact dvd_mul_of_dvd_right h₁₀ 2
          exact h₁₁
        exact dvd_add h₈ h₉
      exact_mod_cast h₆
  
  have h₅ : (|(a : ℤ) - b| ∣ (a + b : ℤ)) ↔ (|(a : ℤ) - b| ∣ (2 * a : ℤ)) := by
    constructor
    · -- Prove the forward direction: if |a - b| ∣ (a + b), then |a - b| ∣ (2 * a)
      intro h₅
      exact h₁ h₅
    · -- Prove the reverse direction: if |a - b| ∣ (2 * a), then |a - b| ∣ (a + b)
      intro h₅
      exact h₃ h₅
  
  have h₆ : ((|(a : ℤ) - b| ∣ (a + b : ℤ) ↔ |(a : ℤ) - b| ∣ (2 * a : ℤ)) ∧ |(a : ℤ) - b| ∣ (a + b : ℤ)) ↔ (|(a : ℤ) - b| ∣ (2 * b : ℤ)) := by
    constructor
    · -- Prove the forward direction: if the left side is true, then the right side is true
      intro h₆
      have h₇ : |(a : ℤ) - b| ∣ (a + b : ℤ) := by
        exact h₆.2
      have h₈ : |(a : ℤ) - b| ∣ (2 * b : ℤ) := by
        exact h₂ h₇
      exact h₈
    · -- Prove the reverse direction: if the right side is true, then the left side is true
      intro h₆
      have h₇ : |(a : ℤ) - b| ∣ (a + b : ℤ) := by
        have h₈ : |(a : ℤ) - b| ∣ (2 * b : ℤ) := h₆
        have h₉ : |(a : ℤ) - b| ∣ (2 * a : ℤ) := by
          rw [h₄] at *
          exact h₈
        have h₁₀ : |(a : ℤ) - b| ∣ (a + b : ℤ) := h₃ h₉
        exact h₁₀
      have h₈ : (|(a : ℤ) - b| ∣ (a + b : ℤ) ↔ |(a : ℤ) - b| ∣ (2 * a : ℤ)) := by
        exact h₅
      exact ⟨h₈, h₇⟩
  
  simpa [h₅, h₄, h₆] using h₆

lemma strong (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Finset ℕ, M.card = n ∧ 0 ∉ M ∧ ∀ a ∈ M, ∀ b ∈ M, a ≠ b → |(a : ℤ) - b| ∣ a + b := by
  induction' n with n ih
  · exfalso; revert hn; decide
  by_cases nn : n = 1
  · subst n
    norm_num
    exists {1, 2}
  have ty : 2 ≤ n := by omega
  clear hn nn
  obtain ⟨M, cM, n0, alM⟩ := ih ty
  exists (insert (2 * M.prod id) (M.map ⟨fun x => 2 * M.prod id + x, by {
    intro a b c
    simp at c
    clear * - c
    linarith
  }⟩))
  constructor
  · clear * - cM n0
    generalize_proofs aj
    rw [Finset.card_insert_of_not_mem]
    · rw [Finset.card_map]; linarith
    simpa
  -- now we have to do more
  generalize_proofs aj
  constructor
  · simp [n0]
    clear * - n0
    intro ls
    revert n0; simp
    have h : 0 ∈ M := by
      have h₁ : ∃ a ∈ M, a = 0 := by
        -- Use the fact that the product of elements in M is zero to find an element in M that is zero.
        have h₂ : (∏ x ∈ M, x) = 0 := ls
        have h₃ : ∃ a ∈ M, a = 0 := by
          -- Use the lemma `Finset.prod_eq_zero_iff` to find an element in M that is zero.
          have h₄ : ∃ a ∈ M, (a : ℕ) = 0 := by
            -- Use the lemma `Finset.prod_eq_zero_iff` to find an element in M that is zero.
            simpa [Nat.cast_eq_zero] using Finset.prod_eq_zero_iff.mp h₂
          simpa using h₄
        exact h₃
      -- Use the fact that there exists an element in M that is zero to conclude that zero is in M.
      obtain ⟨a, ha, ha'⟩ := h₁
      have h₂ : a = 0 := ha'
      have h₃ : a ∈ M := ha
      have h₄ : 0 ∈ M := by
        -- Since a is in M and a is zero, we can conclude that zero is in M.
        simpa [h₂] using h₃
      exact h₄
    exact h
  generalize_proofs mm
  intro a ha b hb
  simp at ha hb
  obtain ha | ha := ha
  all_goals obtain hb | hb := hb
  · subst a b; simp
  pick_goal 3
  · obtain ⟨aa, bb, cc⟩ := ha
    obtain ⟨AA, BB, CC⟩ := hb
    subst a b
    push_cast; ring_nf
    intro my
    have gj := alM aa bb AA BB (by omega)
    have rst := (djs aa AA).1.1 gj
    have h₁ : |(↑aa : ℤ) - ↑AA| ∣ 2 * (∏ i ∈ M, ↑i) := by
      have h₂ : aa ∣ ∏ i ∈ M, i := by
        apply Finset.dvd_prod_of_mem
        <;> simp_all
      have h₃ : |(↑aa : ℤ) - ↑AA| ∣ 2 * ↑aa := rst
      have h₄ : |(↑aa : ℤ) - ↑AA| ∣ 2 * (∏ i ∈ M, ↑i) := by
        have h₅ : 2 * ↑aa ∣ 2 * (∏ i ∈ M, ↑i) := by
          have h₅₁ : ↑aa ∣ (∏ i ∈ M, ↑i) := by simpa using h₂
          apply Nat.mul_dvd_mul_left
          exact h₅₁
        zify at h₅
        exact dvd_trans h₃ h₅
      exact h₄
    have js := dvd_mul_of_dvd_right h₁ 2
    have kk := dvd_add js gj
    ring_nf; ring_nf at kk
    exact kk
  · obtain ⟨aa, bb, cc⟩ := hb
    rw [← cc]
    intro dd
    subst a; simp
    ring_nf
    simp
    have h₂ : aa ∣ ∏ i ∈ M, i := by
      apply Finset.dvd_prod_of_mem
      <;> simp_all
    zify at h₂
    apply dvd_mul_of_dvd_left
    exact h₂
  · obtain ⟨aa, bb, cc⟩ := ha
    rw [← cc]
    intro dd
    subst b; simp
    ring_nf
    simp
    have h₂ : aa ∣ ∏ i ∈ M, i := by
      apply Finset.dvd_prod_of_mem
      <;> simp_all
    zify at h₂
    apply dvd_mul_of_dvd_left
    exact h₂

/- Three, Proof: For any $n \in N, n \geqslant 2$, there exists a set $M$ consisting of $n$ distinct natural numbers such that for any $a \in M$ and $b \in M, |a-b|$ divides $a+b$. -/
theorem number_theory_296536 (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Finset ℕ, M.card = n ∧ ∀ a ∈ M, ∀ b ∈ M, a ≠ b → |(a : ℤ) - b| ∣ a + b := by
  obtain ⟨aa, bb⟩ := strong n hn
  use aa
  tauto
